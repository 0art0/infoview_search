module

public import InfoviewSearch.Search.FindCandidates
public import InfoviewSearch.RefreshComponent
public import ProofWidgets.Component.FilterDetails

/-!
# A widget for showing library search results
-/

meta section

namespace InfoviewSearch
open Lean Server Widget ProofWidgets Jsx

inductive Candidates where
  | rw (hyp? : Option Name) (arr : Array RwLemma)
  | grw (hyp? : Option Name) (arr : Array GrwLemma)
  | app (arr : Array AppLemma)
  | appAt (hyp : Name) (arr : Array AppAtLemma)

local instance {α β cmp} [Append β] : Append (Std.TreeMap α β cmp) :=
  ⟨.mergeWith fun _ ↦ (· ++ ·)⟩

open Meta.RefinedDiscrTree in
/-- Combine the results of looking up in various discrimination trees into an Array
of sections of candidates, where each section corresponds to one kind of match with the
discrimination tree. -/
@[inline]
def getCandidatesAux (rootExpr : Expr) (subExpr : SubExpr) (gpos : Array GrwPos)
    (hyp? : Option Name)
    (rw : Expr → MetaM (MatchResult RwLemma)) (grw : Expr → MetaM (MatchResult GrwLemma))
    (app : Expr → MetaM (MatchResult AppLemma)) (appAt : Expr → MetaM (MatchResult AppAtLemma)) :
    MetaM (Array Candidates) := do
  let mut cands : Std.TreeMap Nat (Array Candidates) := {}
  /- The order in which we show the suggestions for the same pattern for different tactics
  depends on the following insertion order.
  We choose the order `grw` => `rw` => `apply(at)`. -/
  if !gpos.isEmpty then
    cands := cands ++ (← grw subExpr.expr).elts.map fun _ ↦ (·.map (.grw hyp?))
  cands := cands ++ (← rw subExpr.expr).elts.map fun _ ↦ (·.map (.rw hyp?))
  if subExpr.pos == .root then
    if let some hyp := hyp? then
      cands := cands ++ (← appAt rootExpr).elts.map fun _ ↦ (·.map (.appAt hyp))
    else
      cands := cands ++ (← app rootExpr).elts.map fun _ ↦ (·.map .app)
  return cands.foldr (init := #[]) fun _ val acc ↦ acc ++ val

def getImportCandidates (rootExpr : Expr) (subExpr : SubExpr) (gpos : Array GrwPos)
    (hyp? : Option Name) : MetaM (Array Candidates) :=
  getCandidatesAux rootExpr subExpr gpos hyp?
    (getImportMatches rwRef) (getImportMatches grwRef)
    (getImportMatches appRef) (getImportMatches appAtRef)

def getCandidates (rootExpr : Expr) (subExpr : SubExpr) (gpos : Array GrwPos)
    (hyp? : Option Name) (pres : PreDiscrTrees) : MetaM (Array Candidates) :=
  getCandidatesAux rootExpr subExpr gpos hyp?
    (getMatches pres.rw.toRefinedDiscrTree) (getMatches pres.grw.toRefinedDiscrTree)
    (getMatches pres.app.toRefinedDiscrTree) (getMatches pres.appAt.toRefinedDiscrTree)

/-- Spawn a task that computes a piece of `Html` to be displayed when finished. -/
@[specialize]
def spawnTask {α} (premise : Premise) (k : MetaM α) : MetaM <| Task (Except Html (Option α)) := do
  let premiseHtml ← premise.toHtml
  let act ← dropM do
    /- Since this task may have been on the queue for a while,
    the first thing we do is check if it has been cancelled already. -/
    Core.checkInterrupted
    /- Each thread counts its own number of heartbeats, so it is important
    to use `withCurrHeartbeats` to avoid stray maxHeartbeats errors. -/
    withCurrHeartbeats do
      try
        return .ok (some (← k))
      catch ex =>
        /- By default, we catch the errors from failed lemma applications
        (appart from runtime exceptions, i.e. max heartbeats or max recursion depth,
        which aren't caught by the `try`-`catch` block).
        The `infoview_search.debug` option allows the user to still see all errors. -/
        if infoview_search.debug.get (← getOptions) then
          throw ex
        return .ok none
  BaseIO.asTask <| act.catchExceptions fun e =>
    return .error <li>
        {premiseHtml} failed:
        <br/>
        <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
      </li>

public inductive SectionsState where
  | rw (s : SectionState Rw.ResultId)
  | grw (s : SectionState Grw.ResultId)
  | app (s : SectionState Apply.ResultId)
  | appAt (s : SectionState ApplyAt.ResultId)

def SectionsState.isFinished : SectionsState → Bool
  | .rw s | .grw s | .app s | .appAt s => s.pending.isEmpty

def SectionsState.hasProgressed : SectionsState → BaseIO Bool
  | .rw s | .grw s | .app s | .appAt s => s.pending.anyM IO.hasFinished

private def Candidates.generateSuggestions (rootExpr : Expr) (subExpr : SubExpr)
    (pasteInfo : PasteInfo) (occ : LOption Nat)
    (source : Source) (gpos : Array GrwPos) : Candidates → MetaM SectionsState
  | .rw hyp? arr => do
    .rw <$> .new source <$> arr.mapM fun lem ↦
      spawnTask lem.name <| Rw.generateSuggestion rootExpr subExpr pasteInfo hyp? occ lem
  | .grw hyp? arr => do
    .grw <$> .new source <$> arr.mapM fun lem ↦
      spawnTask lem.name <| Grw.generateSuggestion rootExpr subExpr pasteInfo gpos hyp? occ lem
  | app arr => do
    .app <$> .new source <$> arr.mapM fun lem ↦
      spawnTask lem.name <| Apply.generateSuggestion rootExpr pasteInfo lem
  | appAt hyp arr => do
    .appAt <$> .new source <$> arr.mapM fun lem ↦
      spawnTask lem.name <| ApplyAt.generateSuggestion rootExpr pasteInfo hyp lem

/-- While the suggestions are computed, `WidgetState` is used to keep track of the progress.
Initially, it contains a bunch of unfinished `Task`s, and with each round of `updateWidgetState`,
the finished tasks are stored as results in each `SectionsState`. -/
public structure WidgetState where
  /-- The states of the sections in the widget. -/
  sections : Array SectionsState
  /-- The sections corresponding to imported theorems. These are in a separate task, because
  they may take a long time to evaluate. Once evaluated, these are appended to `sections`. -/
  importTask? : Option (Task (Except Exception <| Array SectionsState))
  /-- The HTML shown at the drop-down above the suggestions. -/
  header : Html

set_option linter.style.emptyLine false in
public def initializeWidgetState (rootExpr : Expr) (subExpr : SubExpr) (pasteInfo : PasteInfo)
    (occ : LOption Nat) (fvarId? : Option FVarId) (parentDecl? : Option Name) :
    MetaM WidgetState := do
  Core.checkSystem "infoview_search"
  let mut sections := #[]

  let gpos ← getGrwPos? rootExpr subExpr fvarId?.isSome
  let choice : Choice := {
    rw := true
    grw := !gpos.isEmpty
    app := subExpr.pos == .root && fvarId?.isNone
    appAt := subExpr.pos == .root && fvarId?.isSome
  }
  let pres ← computeLCtxDiscrTrees choice fvarId?
  let hyp? ← fvarId?.mapM (·.getUserName)
  Core.checkSystem "infoview_search"
  for cand in ← getCandidates rootExpr subExpr gpos hyp? pres do
    sections := sections.push
      (← cand.generateSuggestions rootExpr subExpr pasteInfo occ .hypothesis gpos)

  let pres ← computeModuleDiscrTrees choice parentDecl?
  Core.checkSystem "infoview_search"
  for cand in ← getCandidates rootExpr subExpr gpos hyp? pres do
    sections := sections.push
      (← cand.generateSuggestions rootExpr subExpr pasteInfo occ .fromFile gpos)

  Core.checkSystem "infoview_search"
  let importTask? := some <| ← EIO.asTask <| ← dropM (m := MetaM) do
    computeImportDiscrTrees choice
    (← getImportCandidates rootExpr subExpr gpos hyp?).mapM
      (·.generateSuggestions rootExpr subExpr pasteInfo occ .fromImport gpos)

  return { sections, importTask?, header :=
    <span> Lemma suggestions for <InteractiveCode fmt={← ppExprTagged subExpr.expr}/>: </span> }

/-- If `state.importTask?` has been evaluated, append the result to `section`. -/
def updateImportTask (state : WidgetState) : EIO Exception WidgetState := do
  if let some importTask := state.importTask? then
    if ← IO.hasFinished importTask then
      let sections ← EIO.ofExcept importTask.get
      return { state with importTask? := none, sections := state.sections ++ sections }
  return state

/-- Look at all of the pending `Task`s and if any of them gave a result, add this to the state. -/
def updateWidgetState (state : WidgetState) : MetaM WidgetState := do
  let state ← updateImportTask state
  let sections ← state.sections.mapM fun
    | .rw s => .rw <$> s.update (·.isDuplicate ·)
    | .grw s => .grw <$> s.update (·.isDuplicate ·)
    | .app s => .app <$> s.update (·.isDuplicate ·)
    | .appAt s => .appAt <$> s.update (·.isDuplicate ·)
  return { state with sections }

public def WidgetState.render (state : WidgetState)
    (ppSubExpr : CodeWithInfos) : Html :=
  <FilterDetails
    summary={state.header}
    all={go false state ppSubExpr}
    filtered={go true state ppSubExpr}
    initiallyFiltered={true} />
where
  /-- Render all of the sections of lemma suggestions -/
  go (filter : Bool) (state : WidgetState)
      (ppSubExpr : CodeWithInfos) : Html :=
    let htmls := state.sections.filterMap fun
      | .rw s => s.render filter "rw"
      | .grw s => s.render filter "grw"
      | .app s => s.render filter "apply"
      | .appAt s => s.render filter "apply at"
    let htmls := if state.importTask?.isNone then htmls else
      htmls.push <| .text "Imported theorems are being loaded..."
    if htmls.isEmpty then
      <p> No lemma suggestions found for <InteractiveCode fmt={ppSubExpr}/> </p>
    else
      .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls

/-- Repeatedly run `updateWidgetState` until there is an update, and then return the result. -/
public partial def WidgetState.repeatRefresh (state : WidgetState)
    (ppSubExpr : CodeWithInfos) (token : RefreshToken) : MetaM Unit := do
  -- If there is nothing to compute, return the final (empty) display
  token.refresh (state.render ppSubExpr)
  let mut state := state
  while !state.sections.all (·.isFinished) || state.importTask?.isSome do
    Core.checkSystem "infoview_search"
    -- Wait until some task has finished
    while !(← liftM <| state.sections.anyM (·.hasProgressed) <||> match state.importTask? with
        | none => pure false | some importTask => IO.hasFinished importTask) do
      IO.sleep 10
      Core.checkSystem "infoview_search"
    state ← updateWidgetState state
    token.refresh (state.render ppSubExpr)

end InfoviewSearch
