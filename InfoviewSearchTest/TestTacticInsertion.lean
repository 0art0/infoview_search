import Lean

open Lean Elab Command Meta Tactic

deriving instance Repr for ElabInfo

def getNearestTacticElabInfo (fileContents : String) (pos : Lsp.Position) : IO ElabInfo := do
  -- Parse the header of the provided file
  let context := Parser.mkInputContext fileContents (fileName := "test.lean")
  let (header, state, messages) ← Parser.parseHeader context
  let text := context.fileMap
  let (environment, messages) ← processHeader header {} messages context
  -- Process the remaining file
  let commandState := { Command.mkState environment messages with infoState := { enabled := true } }
  let s ← IO.processCommands context state commandState
  let trees : List InfoTree := s.commandState.infoState.trees.toList
  let goalsAt := trees.flatMap (·.goalsAt? text (text.lspPosToUtf8Pos pos))
  if h : goalsAt.length = 0 then -- TODO: Use `goalsAt.isEmpty` instead
    throw <| IO.userError "No goals found at the given position"
  else
    IO.println goalsAt.length
    let nearestGoalsAt := goalsAt[0]
    return nearestGoalsAt.tacticInfo.toElabInfo

def testFile : String :=
"import Lean

open Lean Elab Command Meta Tactic

example : 1 + 1 = 2 := by
  skip
  skip
  "

#eval getNearestTacticElabInfo testFile { line := 8, character := 2 }
