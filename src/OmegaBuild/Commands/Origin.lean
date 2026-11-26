module

public meta import Lean.Elab.Command

public meta section

namespace OmegaBuild

open Lean

/-- Independent official modules can emit the same name. The importer's owner
index and its active term can come from different copies. Read the stored entry. -/
def declaredIn (env : Environment) (name owner : Name) : Bool := Id.run do
  let some expected := env.getModuleIdx? owner | return false
  let some info := env.find? name | return false
  let some entry := env.header.moduleData[expected]!.constants.find? (·.name == name) | return false
  if let .thmInfo a := entry then
    let .thmInfo b := info | return false
    -- Structural equality includes binder names and annotations. The kernel identifies
    -- proofs of the same proposition, including distinct compiler-generated proofs.
    return a.levelParams == b.levelParams && a.type.equal b.type
  unless entry == info && entry.type.equal info.type do return false
  if let .recInfo a := entry then
    let .recInfo b := info | return false
    return (a.rules.zip b.rules).all fun (x, y) => x.rhs.equal y.rhs
  return (entry.value? (allowOpaque := true)).map ExprStructEq.mk ==
    (info.value? (allowOpaque := true)).map ExprStructEq.mk

/-- Give mixed consumers a native overload for every declaration exported by an admitted port. -/
def exportNativePorts : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let mut exports := env
  for provider in env.header.moduleNames, i in [:env.header.moduleNames.size] do
    unless provider.getRoot == `OmegaMathlib do continue
    let upstream := provider.replacePrefix `OmegaMathlib `Mathlib
    for (alias, target) in aliasExtension.getModuleEntries env i do
      unless alias.getRoot == `OmegaMathlib do continue
      let native := alias.replacePrefix `OmegaMathlib .anonymous
      let strict := alias.replacePrefix `OmegaMathlib `Omega
      unless (env.getModuleIdxFor? native).any (env.header.moduleNames[·]! == upstream) &&
          declaredIn env native upstream do
        throwError "{alias} requires {native} in {upstream}"
      unless target == native || (target == strict && env.getModuleIdxFor? strict == some i &&
          declaredIn env strict provider) do
        throwError "{provider} exports an unexpected target {target} as {alias}"
      if target != native then
        let nativeInfo ← getConstInfo native
        let portInfo ← getConstInfo target
        let nativeType := nativeInfo.type.instantiateLevelParams nativeInfo.levelParams
          (portInfo.levelParams.map Level.param)
        -- If Lean cannot distinguish the two signatures, keep the canonical port unambiguous.
        unless portInfo.numLevelParams == nativeInfo.numLevelParams &&
            Kernel.isDefEqGuarded env {} portInfo.type nativeType do
          exports := addAlias exports alias native
  setEnv exports

end OmegaBuild
