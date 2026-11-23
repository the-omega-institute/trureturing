import Lean
import Lean.Replay

open Lean

/-- Read only artifacts in the target search path. The inspector's own environment
is used to run this program, while the audited environment starts with the named root. -/
def main (args : List String) : IO Unit := do
  let root :: path :: expected := args
    | throw <| IO.userError "usage: Audit ROOT SEARCH_PATH EXPECTED_MODULE..."
  searchPathRef.set (System.SearchPath.parse path)
  let env ← importModules #[{ module := root.toName }] {}
  let actual := env.allImportedModuleNames.toList.map Name.toString
  unless actual.mergeSort == expected.mergeSort do
    throw <| IO.userError s!"module closure differs: found {actual}, expected {expected}"
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
  IO.println s!"{root}: {actual.length} modules, {count} declarations, zero axioms, fresh kernel replay passed"
