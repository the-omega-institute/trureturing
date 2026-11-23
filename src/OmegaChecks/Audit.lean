import Lean
import Lean.Replay

open Lean

private def isStrict (name : Name) : Bool :=
  name.getRoot == `OmegaMath || name.getRoot == `OmegaInit

private def isOriginalMath (env : Environment) (owner : Name) : Bool := Id.run do
  unless owner.getRoot == `OmegaMath do return false
  let some docs := getModuleDoc? env owner | return false
  let some first := docs[0]? | return false
  return (first.doc.splitOn "\n").head!.trimAscii == "Omega original."

/-- Compare public names and defining modules in a separate upstream environment. -/
private def checkUpstreamNames (strict : Environment) : IO Unit := do
  let sysroot ← findSysroot
  let lib ← getLibDir sysroot
  let foundation := strict.allImportedModuleNames.filter (·.getRoot == `OmegaInit)
  for owner in foundation do
    let official := owner.replacePrefix `OmegaInit `Init
    unless ← (modToFilePath lib official "olean").pathExists do
      throw <| IO.userError s!"no official module {official} for {owner}"
  let mut bindings := #[]
  let mut owners := #[]
  let originals := strict.allImportedModuleNames.filter (isOriginalMath strict)
  for (name, _) in strict.constants.toList do
    let some idx := strict.getModuleIdxFor? name | continue
    let owner := strict.header.moduleNames[idx]!
    if !isStrict owner || isPrivateName name || name.isInternal then continue
    unless name.getRoot == `Omega do
      throw <| IO.userError s!"public name outside Omega: {name} in {owner}"
    if originals.contains owner then continue
    let upstream := if owner.getRoot == `OmegaInit then `Init else `Mathlib
    let official := owner.replacePrefix owner.getRoot upstream
    bindings := bindings.push (name, official)
    if !owners.contains official then owners := owners.push official
  if owners.isEmpty then return
  let mathlib := owners.filter (·.getRoot == `Mathlib)
  if mathlib.isEmpty then
    searchPathRef.set [lib]
  else
    let targets := mathlib.map fun name => s!"@mathlib/+{name}:olean"
    let proc ← IO.Process.spawn { cmd := "lake", args := #["build"] ++ targets }
    unless (← proc.wait) == 0 do throw <| IO.userError s!"failed to build upstream modules {mathlib}"
    initSearchPath sysroot [lib]
  let reference ← importModules (owners.map fun moduleName => {module := moduleName}) {}
  for (name, owner) in bindings do
    let counterpart := name.replacePrefix `Omega Name.anonymous
    let some idx := reference.getModuleIdxFor? counterpart
      | throw <| IO.userError s!"missing official declaration {counterpart} in {owner} for {name}"
    let actual := reference.header.moduleNames[idx]!
    unless actual == owner do
      throw <| IO.userError s!"official owner of {counterpart} is {actual}, expected {owner}"
  IO.println s!"Upstream names and owning modules matched for {bindings.size} declarations in {owners}."

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
      unless isStrict name.toName do
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
  checkUpstreamNames env
  IO.println s!"{label}: {actual.length} modules, {count} declarations, zero axioms, fresh kernel replay passed"

private def testLibrary (selected : List String) : IO Unit := do
  if selected.isEmpty then
    throw <| IO.userError "pass a module scope, for example: lake test -- OmegaMath.Projective"
  let strict := selected.filter fun name => isStrict name.toName
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
