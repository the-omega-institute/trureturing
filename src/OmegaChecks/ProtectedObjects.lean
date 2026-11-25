import OmegaChecks.Interface
import OmegaChecks.ModuleSurface

/-! Compare every OmegaMath object with the compiled protected revision on the same backend. -/

open Lean

namespace OmegaChecks.ProtectedObjects

private def proof (env : Environment) (info : ConstantInfo) : Bool :=
  (info.isTheorem || info matches .defnInfo _ | .opaqueInfo _) &&
    (Kernel.check env {} info.type).toOption.any (Kernel.isDefEqGuarded env {} (mkSort .zero))

private def directPort (env : Environment) (ports : NameSet) (info : ConstantInfo) : Bool := Id.run do
  let .defnInfo d := info | return false
  let .const target levels := d.value | return false
  let some upstream := env.find? target | return false
  return d.safety == .safe && d.hints == .abbrev && ports.contains target &&
    levels == d.levelParams.map Level.param && upstream.numLevelParams == levels.length &&
    Kernel.isDefEqGuarded env {} d.type (upstream.type.instantiateLevelParams upstream.levelParams levels)

private def portTargets (env : Environment) : NameSet := Id.run do
  let mut targets := {}
  for owner in env.header.moduleNames, i in [:env.header.moduleNames.size] do
    if owner.getRoot == `OmegaMathlib then
      for (alias, target) in aliasExtension.getModuleEntries env i do
        if alias.getRoot == `OmegaMathlib then targets := targets.insert target
  return targets

/-- Check the objects that appear in a newly published statement. If it uses another
proof as an index, follow the type of that proof. Proof implementations remain private. -/
private def checkStatement (env : Environment) (ports : NameSet) (published : Name)
    (type : Expr) : IO Unit := do
  let mut pending := type.getUsedConstants
  let mut seen : NameSet := {}
  while let some name := pending.back? do
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some owner := env.getModuleIdxFor? name | throw <| IO.userError s!"missing owner of {name}"
    let moduleName := env.header.moduleNames[owner]!
    if [`Init, `Mathlib].contains moduleName.getRoot || ports.contains name ||
        (moduleName.getRoot == `OmegaInit && !isPrivateName name && !name.isInternal) then continue
    let some info := env.find? name | throw <| IO.userError s!"missing statement object {name}"
    if directPort env ports info then continue
    if proof env info then
      pending := pending ++ info.type.getUsedConstants
    else
      throw <| IO.userError s!"publish {published} in D5: statement uses project object {name} from {moduleName}"

/-- A bridge is a theorem about the old compiled body and the new port, quantified over
all inputs. Strict proofs use the independently checked strict versions of Eq and Iff. -/
private def checkBridge (env : Environment) (before after : ConstantInfo) (decls : Array Name) : IO Name := do
  unless before.numLevelParams == after.numLevelParams &&
      Kernel.isDefEqGuarded env {} (before.type.instantiateLevelParams before.levelParams
        (after.levelParams.map Level.param)) after.type do
    throw <| IO.userError s!"protected type changed: {before.name}"
  let oldValue := before.value!.instantiateLevelParams before.levelParams (after.levelParams.map Level.param)
  let strict := env.contains `Omega.Eq
  let forms : MetaM (Array Expr) := Meta.forallTelescope after.type fun xs result => do
    let lhs := mkAppN oldValue xs
    let rhs := mkAppN after.value! xs
    let eq ← Meta.mkAppM (if strict then `Omega.Eq else `Eq) #[lhs, rhs]
    let mut expected := #[← Meta.mkForallFVars xs eq]
    if result.isProp then
      expected := expected.push (← Meta.mkForallFVars xs
        (mkApp2 (mkConst (if strict then `Omega.Iff else `Iff)) lhs rhs))
    return expected
  let expected ← forms.run' |>.toIO' {fileName := "<protected object>", fileMap := default} {env}
  for name in decls do
    let some (.thmInfo cert) := env.find? name | continue
    if cert.levelParams.length != after.numLevelParams then continue
    let typ := cert.type.instantiateLevelParams cert.levelParams (after.levelParams.map Level.param)
    if expected.any (Kernel.isDefEqGuarded env {} typ) then
      let axioms ← (collectAxioms name : CoreM _).toIO' {fileName := "<protected object>", fileMap := default} {env}
      if axioms.all (fun ax => !strict && #[`propext, `Quot.sound, `Classical.choice].contains ax) then return name
  throw <| IO.userError s!"missing all-input correspondence for protected object {before.name}"

private def aliases (env : Environment) (idx : ModuleIdx) : List (Name × Name) :=
  (aliasExtension.getModuleEntries env idx).toList

def check (old new : Environment) (baseRoots newRoots : Array Name) : IO Unit := do
  let ports := portTargets new
  for m in baseRoots do
    unless newRoots.contains m do throw <| IO.userError s!"removed protected OmegaMath module {m}"
  for m in newRoots do
    unless m.getRoot == `OmegaMath do throw <| IO.userError s!"invalid protected comparison root {m}"
    let some idx := new.getModuleIdx? m | throw <| IO.userError s!"missing candidate module {m}"
    let newNames := new.header.moduleData[idx]!.constNames
    let oldIdx := if baseRoots.contains m then old.getModuleIdx? m else none
    if let some i := oldIdx then
      let previous := old.header.moduleData[i]!.imports
      let current := new.header.moduleData[idx]!.imports
      if previous != current then
        let visible ← ModuleSurface.publicClosure new m
        for dep in previous do
          if dep.isExported && dep.module.getRoot == `OmegaMath && !visible.contains dep.module then
            throw <| IO.userError s!"{m} no longer re-exports protected module {dep.module}"
    let oldNames := oldIdx.map (fun i => old.header.moduleData[i]!.constNames) |>.getD #[]
    let mut bridges : NameSet := {}
    for name in oldNames do
      let some before := old.find? name | throw <| IO.userError s!"missing protected declaration {name}"
      let some after := new.find? name | do
        if isPrivateName name && proof old before then continue
        throw <| IO.userError s!"removed protected declaration {name}"
      unless new.getModuleIdxFor? name == some idx do
        throw <| IO.userError s!"protected declaration {name} changed owning module"
      if before == after then continue
      if before.ctorIdx != after.ctorIdx then
        throw <| IO.userError s!"protected declaration kind changed: {name}"
      if directPort new ports after && before.value? != after.value? then
        bridges := bridges.insert (← checkBridge new before after newNames)
      else
        discard <| Interface.compare new id before after
    let known := NameSet.ofList oldNames.toList
    for name in newNames do
      if known.contains name then continue
      let some info := new.find? name | throw <| IO.userError s!"missing declaration {name}"
      if proof new info then
        if !isPrivateName name && !bridges.contains name then checkStatement new ports name info.type
      else unless directPort new ports info do
        throw <| IO.userError s!"new OmegaMath object {name} in {m}"
    let before := oldIdx.map (aliases old) |>.getD []
    let after := aliases new idx
    for entry in before do
      unless after.contains entry do throw <| IO.userError s!"changed protected export {entry.1}"
    for (alias, target) in after do
      if before.contains (alias, target) || ports.contains target then continue
      let some info := new.find? target | throw <| IO.userError s!"missing export target {target}"
      unless proof new info do throw <| IO.userError s!"new OmegaMath export {alias} has an unverified target {target}"
      checkStatement new ports alias info.type
  IO.println s!"Protected objects checked in {newRoots.size} OmegaMath modules."

end OmegaChecks.ProtectedObjects
