import Lean
import OmegaChecks.InitCompiler.RootNames

open Lean

private def portName (n : Name) : Name :=
  if OmegaChecks.InitCompiler.RootNames.usesRoot n then n else `Omega ++ n

/-- Check ordinary public visibility of the ported Init names from both generated entry points. -/
def main (args : List String) : IO Unit := do
  let output :: basis :: modules := args | throw <| IO.userError "expected consumer library, basis library and modules"
  let ports := modules.toArray.map String.toName
  unless ports.contains `OmegaInit do throw <| IO.userError "missing OmegaInit entry point"
  let publicImports := fun (names : Array Name) => names.map fun name => {module := name : Import}
  searchPathRef.set [← getLibDir (← findSysroot)]
  let official ← importModules (publicImports #[`Init]) {} (level := .exported)
  let original ← importModules (publicImports (ports.map (·.replacePrefix `OmegaInit `Init))) {} (level := .exported)
  searchPathRef.set [output, basis]
  let available ← importModules (publicImports ports) {} (level := .exported)
  let roots ← #[`OmegaInit, `OmegaMath].mapM fun root => do
    return (root, ← importModules (publicImports #[root]) {} (level := .exported))
  let mut exported := 0
  let mut separate := 0
  let mut structures := 0
  for (root, env) in roots do
    for owner in official.header.moduleNames do
      let originalIdx := (official.getModuleIdx? owner).get!
      let expected := (aliasExtension.getModuleEntries official originalIdx).filterMap fun (alias, target) =>
        if env.contains (portName target) then some (portName alias, portName target) else none
      let idx := env.getModuleIdx? (owner.replacePrefix `Init `OmegaInit)
      let aliases := official.header.moduleData[originalIdx]!.constNames.filterMap fun n => do
        let entry ← OmegaChecks.InitCompiler.RootNames.aliasFor? n
        let i ← idx
        guard (env.header.moduleData[i]!.constNames.contains entry.2)
        return entry
      let actual := idx.map fun i => aliasExtension.getModuleEntries env i
      let actual := actual.getD #[]
      unless (actual.filter (fun pair => !aliases.contains pair)) == expected &&
          actual.size == expected.size + aliases.size && aliases.all actual.contains do
        throw <| IO.userError s!"exported aliases differ from {owner} under import {root}"
  for (name, _) in available.constants.toList do
    unless name.getRoot == `Omega || OmegaChecks.InitCompiler.RootNames.usesRoot name do continue
    let upstream := name.replacePrefix `Omega .anonymous
    unless original.contains upstream do continue
    let expected := official.contains upstream
    for (root, env) in roots do
      unless env.contains name == expected do
        let issue := if expected then "missing from" else "unexpectedly exported by"
        throw <| IO.userError s!"{name} is {issue} import {root} compared with import Init"
      if expected && (getStructureInfo? official upstream).isSome && (getStructureInfo? env name).isNone then
        throw <| IO.userError s!"missing structure fields for {name} under import {root}"
      if expected && (official.getProjectionFnInfo? upstream).isSome && (env.getProjectionFnInfo? name).isNone then
        throw <| IO.userError s!"missing projection metadata for {name} under import {root}"
      if expected then
        for (label, hasTag) in [("match_pattern", hasMatchPatternAttribute),
            ("elab_as_elim", Elab.Term.elabAsElim.hasTag), ("never_extract", hasNeverExtractAttribute), ("auxiliary recursor", isAuxRecursor)] do
          unless hasTag env name == hasTag official upstream do
            throw <| IO.userError s!"{label} mismatch for {name} under import {root}"
    if expected && (getStructureInfo? official upstream).isSome then structures := structures + 1
    if expected then exported := exported + 1 else separate := separate + 1
  IO.println s!"OmegaInit and OmegaMath public imports match Init for {exported} root names and {separate} separately imported names"
  IO.println s!"Verified the field registrations of {structures} publicly imported structures"
