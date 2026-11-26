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

/-- Imported modules are in dependency order. Keep one import path to the explicit selection. -/
def mathlibOnlyPaths (env : Environment) : NameMap (List Name) := Id.run do
  let mut paths : NameMap (List Name) := {}
  for owner in env.header.moduleNames, data in env.header.moduleData, i in [:env.header.moduleNames.size] do
    if isMathlibOnly env i then
      paths := paths.insert owner [owner]
    else
      for dep in data.imports do
        if let some path := paths.find? dep.module then
          paths := paths.insert owner (owner :: path)
          break
  return paths

/-- Compile this module and all its importers only with the official Mathlib backend. -/
elab "compile_only_with_mathlib" : command =>
  modifyEnv fun env => mathlibOnlyExt.setState env true

end OmegaBuild
