import Lean
import Lean.Replay

open Lean

private def isStrict (name : String) : Bool :=
  name.toName.getRoot == `OmegaMath || name.toName.getRoot == `OmegaInit

/-- Compare names and declaring modules against a separate environment of installed Lean artifacts. -/
private def checkFoundationNames (strict : Environment) : IO Unit := do
  let lib ← getLibDir (← findSysroot)
  let foundation := strict.allImportedModuleNames.filter (·.getRoot == `OmegaInit)
  for owner in foundation do
    let official := owner.replacePrefix `OmegaInit `Init
    unless ← (modToFilePath lib official "olean").pathExists do
      throw <| IO.userError s!"no official module {official} for {owner}"
  let mut bindings := #[]
  let mut owners := #[]
  for (name, _) in strict.constants.toList do
    let some idx := strict.getModuleIdxFor? name | continue
    let owner := strict.header.moduleNames[idx]!
    if owner.getRoot != `OmegaInit || isPrivateName name || name.isInternal then continue
    unless name.getRoot == `Omega do
      throw <| IO.userError s!"public foundation name outside Omega: {name} in {owner}"
    let official := owner.replacePrefix `OmegaInit `Init
    bindings := bindings.push (name, official)
    if !owners.contains official then owners := owners.push official
  if owners.isEmpty then return
  searchPathRef.set [lib]
  let reference ← importModules (owners.map fun moduleName => {module := moduleName}) {}
  for (name, owner) in bindings do
    let counterpart := name.replacePrefix `Omega Name.anonymous
    let some idx := reference.getModuleIdxFor? counterpart
      | throw <| IO.userError s!"missing official declaration {counterpart} in {owner} for {name}"
    let actual := reference.header.moduleNames[idx]!
    unless actual == owner do
      throw <| IO.userError s!"official owner of {counterpart} is {actual}, expected {owner}"
  IO.println s!"Official Init names and owning modules matched for {bindings.size} declarations."

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
  checkFoundationNames env
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
