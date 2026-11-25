module

public meta import Lean.Compiler.ModPkgExt
public meta import Lean.Elab.Command

public meta section

namespace OmegaBuild

open Lean

private initialize mathlibOnlyExt : ModuleEnvExtension Bool ← registerModuleEnvExtension (pure false)

/-- Read the backend explicitly selected by an imported module. -/
def isMathlibOnly (env : Environment) (idx : ModuleIdx) : Bool :=
  (mathlibOnlyExt.getStateByIdx? env idx).getD false

/-- Compile this module and all its importers only with the official Mathlib backend. -/
elab "compile_only_with_mathlib" : command =>
  modifyEnv fun env => mathlibOnlyExt.setState env true

end OmegaBuild
