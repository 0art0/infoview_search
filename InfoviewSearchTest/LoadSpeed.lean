module

public import InfoviewSearch
import all InfoviewSearch.FindCandidates
import Mathlib

public meta section

namespace InfoviewSearch
open Lean

def measureImport (choice : Choice) : MetaM (Nat × PreDiscrTrees) := do
  let t0 ← IO.monoMsNow
  let (tasks, _) ← foldEnv {} (Entries.addConst choice) 5000
  let pre : PreDiscrTrees := tasks.foldl (·.append ·.get) {}
  return ((← IO.monoMsNow) - t0, pre)

def loadAll : MetaM Unit := do
  let (rw, _) ← measureImport { rw := true, grw := false, app := false, appAt := false }
  let (grw, _) ← measureImport { rw := false, grw := true, app := false, appAt := false }
  let (apply, _) ← measureImport { rw := false, grw := false, app := true, appAt := false }
  let (applyAt, _) ← measureImport { rw := false, grw := false, app := false, appAt := true }
  let (all, _) ← measureImport { rw := true, grw := true, app := true, appAt := true }
  logInfo m!"rw: {rw}; grw: {grw}; apply: {apply}; apply at: {applyAt}\n\
    total: {all}"

-- run_meta loadAll

end InfoviewSearch
/-
Some example outputs I got:

rw: 3739; grw: 2256; apply: 3749; apply at: 2934
total: 8963

rw: 4181; grw: 2283; apply: 3934; apply at: 2812
total: 7760

rw: 3983; grw: 2196; apply: 3720; apply at: 2765
total: 9193

rw: 4105; grw: 2250; apply: 3685; apply at: 2997
total: 10960

-/
