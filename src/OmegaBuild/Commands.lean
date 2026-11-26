module

public meta import Lean.Compiler.ModPkgExt
public meta import Lean.Elab.Command
public meta import OmegaBuild.Commands.Origin

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

/-- Select the pinned native declaration of an explicitly named OmegaMathlib port. -/
syntax (name := nativePort) "native% " ident (Parser.Term.explicitUnivSuffix)? : term

@[term_elab nativePort] def elabNativePort : Elab.Term.TermElab := fun stx expectedType? => do
  let id := stx[1]
  let aliasName := id.getId.eraseMacroScopes.replacePrefix `_root_ .anonymous
  unless aliasName.getRoot == `OmegaMathlib do
    throwErrorAt id "expected a qualified OmegaMathlib port"
  let native := aliasName.replacePrefix `OmegaMathlib .anonymous
  let env ← getEnv
  let some nativeIdx := env.getModuleIdxFor? native
    | throwErrorAt id "native Mathlib declaration {native} must be imported"
  let upstream := env.header.moduleNames[nativeIdx]!
  unless upstream.getRoot == `Mathlib && declaredIn env native upstream do
    throwErrorAt id "{native} is not the active declaration from its pinned Mathlib module"
  let provider := upstream.replacePrefix `Mathlib `OmegaMathlib
  let some idx := env.getModuleIdx? provider
    | throwErrorAt id "{aliasName} requires the admitted port module {provider}"
  let strict := aliasName.replacePrefix `OmegaMathlib `Omega
  let authentic := (aliasExtension.getModuleEntries env idx).any fun (alias, target) =>
    alias == aliasName && (target == native ||
      (target == strict && env.getModuleIdxFor? target == some idx && declaredIn env target provider))
  unless authentic do throwErrorAt id "{provider} does not export the verified port {aliasName}"
  let ref := mkCIdentFrom id native
  let ref := if stx[2].isNone then ref.raw else
    mkNode ``Parser.Term.explicitUniv (#[ref.raw] ++ stx[2].getArgs)
  let result ← Elab.Term.elabTerm ref expectedType?
  -- The inferred implicit arguments can make the result an application; the reference
  -- index records an identifier only for a constant expression at its source range.
  Elab.addConstInfo stx native
  return result

end OmegaBuild
