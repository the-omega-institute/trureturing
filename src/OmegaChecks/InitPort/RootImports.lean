import Lean

open Lean

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
  for (name, _) in available.constants.toList do
    unless name.getRoot == `Omega do continue
    let upstream := name.replacePrefix `Omega .anonymous
    unless original.contains upstream do continue
    let expected := official.contains upstream
    for (root, env) in roots do
      unless env.contains name == expected do
        let issue := if expected then "missing from" else "unexpectedly exported by"
        throw <| IO.userError s!"{name} is {issue} import {root} compared with import Init"
    if expected then exported := exported + 1 else separate := separate + 1
  IO.println s!"OmegaInit and OmegaMath public imports match Init for {exported} root names and {separate} separately imported names"
