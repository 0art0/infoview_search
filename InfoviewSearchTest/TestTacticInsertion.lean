module

public import Lean
public import InfoviewSearch.Util

open Lean Elab Command Meta Tactic Server InfoviewSearch

deriving instance Repr for ElabInfo

public meta def testTacticInsertionLogic (fileContents : String) (cursorPos : Lsp.Position)
    (tactic : TSyntax `tactic) (expectedOutput : String)
    (tacticInsertionLogic : TSyntax `tactic → PasteInfo → IO Lsp.TextEdit) : IO Bool := do
  -- Parse the header of the provided file
  let context := Parser.mkInputContext fileContents (fileName := "test.lean")
  let (header, state, messages) ← Parser.parseHeader context
  let text := context.fileMap
  let (environment, messages) ← processHeader header {} messages context
  -- Process the remaining file
  let commandState := { Command.mkState environment messages with infoState := { enabled := true } }
  let s ← IO.processCommands context state commandState
  let trees : List InfoTree := s.commandState.infoState.trees.toList
  let goalsAt := trees.flatMap (·.goalsAt? text (text.lspPosToUtf8Pos cursorPos))
  if h : goalsAt.length = 0 then -- TODO: Use `goalsAt.isEmpty` instead
    throw <| IO.userError "No goals found at the given position"
  else
    IO.println goalsAt.length
    let nearestGoalsAt := goalsAt[0]
    let pasteInfo : PasteInfo := {
      «meta» := { (default : DocumentMeta) with text }
      cursorPos, stx := nearestGoalsAt.tacticInfo.stx }
    let { range, newText, .. } ← tacticInsertionLogic tactic pasteInfo
    return editText fileContents (text.lspRangeToUtf8Range range) newText == expectedOutput
where
  editText (file : String) (range : Lean.Syntax.Range) (newText : String) : String :=
    sorry

private def testFile : String :=
"import Lean

open Lean Elab Command Meta Tactic

example : 1 + 1 = 2 := by
  skip
  skip
  "

private def testFile.expectedOutput : String :=
"import Lean

open Lean Elab Command Meta Tactic

example : 1 + 1 = 2 := by
  skip
  skip
  simp"

-- #eval show MetaM _ from do
--   testTacticInsertionLogic
--     testFile { line := 7, character := 6 }
--     (← `(tactic| simp))
--     testFile.expectedOutput
--     sorry
