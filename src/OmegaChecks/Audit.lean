import Lean
import Lean.Replay

open Lean

private def isStrict (name : String) : Bool :=
  name.toName.getRoot == `OmegaMath || name.toName.getRoot == `OmegaInit

/-- Replay the imported artifacts in an empty kernel environment. -/
private def audit (roots : List String) (path label : String) (expected : Option (List String)) : IO Unit := do
  searchPathRef.set (System.SearchPath.parse path)
  let env ← importModules (roots.toArray.map fun name => { module := name.toName }) {}
  let actual := env.allImportedModuleNames.toList.map Name.toString
  if let some modules := expected then
    unless actual.mergeSort == modules.mergeSort do
      throw <| IO.userError s!"module closure differs: found {actual}, expected {modules}"
  else
    for name in actual do
      unless isStrict name do
        throw <| IO.userError s!"unexpected strict library import {name}"
  let check : CoreM Nat := do
    let mut count := 0
    for (name, info) in env.constants.toList do
      if info.isUnsafe || info matches .axiomInfo _ | .quotInfo _ then
        throwError "inadmissible declaration {name}"
      let axioms ← collectAxioms name
      unless axioms.isEmpty do
        throwError "{name} depends on {axioms}"
      count := count + 1
    return count
  let count ← check.toIO' {fileName := "<audit>", fileMap := default} {env}
  discard <| (← mkEmptyEnvironment).toKernelEnv.replay env.constants.map₁
  IO.println s!"{label}: {actual.length} modules, {count} declarations, zero axioms, fresh kernel replay passed"

private def testLibrary (selected : List String) : IO Unit := do
  if selected.isEmpty then
    throw <| IO.userError "pass a module scope, for example: lake test -- OmegaMath.Projective"
  let strict := selected.filter isStrict
  let roots := if strict.isEmpty && selected.contains "OmegaChecks.Audit" then ["OmegaInit.Prelude"] else strict
  if roots.isEmpty then return
  let proc ← IO.Process.spawn { cmd := "lake", args := #["build"] ++ roots.toArray.map ("+" ++ ·) }
  unless (← proc.wait) == 0 do throw <| IO.userError "strict library build failed"
  audit roots ".lake/build/lib/lean" "Omega" none

def main (args : List String) : IO Unit := do
  if let "--exact" :: root :: path :: expected := args then
    audit [root] path root (some expected)
  else
    testLibrary args
