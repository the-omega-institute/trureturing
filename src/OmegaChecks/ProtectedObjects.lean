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

/-- Preserve the weakest transparency mode in which an ordinary client could unfold the
old declaration, including any intermediate definitions in the new public representation. -/
private def keepsReduction (old new : Environment) (before after : ConstantInfo) : IO Bool := do
  let levels := after.levelParams.map Level.param
  let expected := before.value!.instantiateLevelParams before.levelParams levels
  let sameBody := expected == after.value!
  if sameBody && getReducibilityStatusCore old before.name == getReducibilityStatusCore new after.name then
    return true
  let context : Core.Context := {fileName := "<public reduction>", fileMap := default}
  for mode in #[Meta.TransparencyMode.reducible, .instances, .implicit, .default, .all] do
    let cfg : Meta.Config := {transparency := mode}
    if ← (Meta.canUnfoldDefault cfg before).toIO' context {env := old} then
      unless ← (Meta.canUnfoldDefault cfg after).toIO' context {env := new} do return false
      if sameBody then return true
      let check := Meta.withTransparency mode <| Meta.isDefEq (mkConst after.name levels) expected
      return ← check.run' |>.toIO' context {env := new}
  return false

/-- A client can unfold an exposed historical definition. Locate that same
computational representation in a frozen D5 module, together with a kernel
proof relating its public name to the new upstream object at all inputs. -/
private def checkLegacy (env oldPublic publicEnv : Environment) (owners : Array Name)
    (before after : ConstantInfo) : IO Unit := do
  let levels := after.levelParams.map Level.param
  let prior := fun (e : Expr) => e.instantiateLevelParams before.levelParams levels
  unless before.numLevelParams == after.numLevelParams &&
      Kernel.isDefEqGuarded env {} (prior before.type) after.type do
    throw <| IO.userError s!"protected type changed: {before.name}"
  let oldValue := prior before.value!
  let target := after.value!
  if Kernel.isDefEqGuarded publicEnv {} oldValue target && (← keepsReduction oldPublic publicEnv before after) then return
  let mut legacy : NameSet := {}
  let mut decls := #[]
  for owner in owners do
    unless owner.getRoot == `D5 do throw <| IO.userError s!"invalid legacy owner {owner}"
    let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing D5 owner {owner}"
    for n in env.header.moduleData[idx]!.constNames do
      if isPrivateName n || n.isInternalOrNum then continue
      let some info := env.find? n | continue
      if info.numLevelParams != after.numLevelParams then continue
      let some visible := publicEnv.find? n | continue
      match info, visible with
      | .defnInfo _, .defnInfo d =>
        if d.safety == .safe &&
            Kernel.isDefEqGuarded env {} (d.type.instantiateLevelParams d.levelParams levels) after.type &&
            Kernel.isDefEqGuarded publicEnv {} (d.value.instantiateLevelParams d.levelParams levels) oldValue &&
            (← keepsReduction oldPublic publicEnv before visible) then
          legacy := legacy.insert n
      | .thmInfo t, _ => decls := decls.push t
      | _, _ => pure ()
  if legacy.isEmpty then
    throw <| IO.userError s!"missing observable D5 representation for protected object {before.name}"
  let strict := env.contains `Omega.Eq
  for cert in decls do
    let typ := cert.type.instantiateLevelParams cert.levelParams levels
    let refs := typ.getUsedConstants
    unless refs.contains target.constName! do continue
    for rep in refs.filter legacy.contains do
      let forms := Meta.forallTelescope after.type fun xs result => do
        let lhs := mkAppN (mkConst rep levels) xs
        let rhs := mkAppN target xs
        let eq ← Meta.mkAppM (if strict then `Omega.Eq else `Eq) #[lhs, rhs]
        let mut expected := #[← Meta.mkForallFVars xs eq]
        if result.isProp then
          expected := expected.push (← Meta.mkForallFVars xs
            (mkApp2 (mkConst (if strict then `Omega.Iff else `Iff)) lhs rhs))
        return expected
      let expected ← (forms : MetaM _).run' |>.toIO' {fileName := "<protected object>", fileMap := default} {env}
      if expected.any (Kernel.isDefEqGuarded env {} typ) then
        let axioms ← (collectAxioms cert.name : CoreM _).toIO' {fileName := "<protected object>", fileMap := default} {env}
        if axioms.all (fun ax => !strict && #[`propext, `Quot.sound, `Classical.choice].contains ax) then
          return
  throw <| IO.userError s!"missing all-input correspondence in D5 for protected object {before.name}"

private def aliases (env : Environment) (idx : ModuleIdx) : List (Name × Name) :=
  (aliasExtension.getModuleEntries env idx).toList

def check (old new publicOld publicNew : Environment) (baseRoots newRoots : Array Name)
    (comparison publicComparison : Environment) (legacyOwners : Array Name) : IO Unit := do
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
          if dep.isExported && (dep.module.getRoot == `OmegaMath || ModuleSurface.isBasis dep.module) &&
              !visible.contains dep.module then
            throw <| IO.userError s!"{m} no longer re-exports protected module {dep.module}"
    let oldNames := oldIdx.map (fun i => old.header.moduleData[i]!.constNames) |>.getD #[]
    for name in oldNames do
      let some before := old.find? name | throw <| IO.userError s!"missing protected declaration {name}"
      let some after := new.find? name | do
        if isPrivateName name && proof old before then continue
        throw <| IO.userError s!"removed protected declaration {name}"
      unless new.getModuleIdxFor? name == some idx do
        throw <| IO.userError s!"protected declaration {name} changed owning module"
      -- The private artifact retains bodies even when ordinary importers cannot reduce them.
      if let some exposed := publicOld.find? name then
        let some visible := publicNew.find? name | throw <| IO.userError s!"protected public declaration hidden: {name}"
        if exposed matches .defnInfo _ then
          unless visible matches .defnInfo _ do
            throw <| IO.userError s!"protected definition no longer exposes its body: {name}"
          unless directPort new ports after || (← keepsReduction publicOld publicNew exposed visible) do
            throw <| IO.userError s!"protected public unfolding changed: {name}"
          unless directPort new ports after || Kernel.isDefEqGuarded publicNew {}
              (exposed.value!.instantiateLevelParams exposed.levelParams (visible.levelParams.map Level.param))
              visible.value! do
            throw <| IO.userError s!"protected public reduction changed: {name}"
      if before == after then continue
      if before.ctorIdx != after.ctorIdx then
        throw <| IO.userError s!"protected declaration kind changed: {name}"
      if directPort new ports after && before.value? != after.value? then
        checkLegacy comparison publicOld publicComparison legacyOwners before after
      else
        discard <| Interface.compare new id before after
    let known := NameSet.ofList oldNames.toList
    for name in newNames do
      if known.contains name then continue
      let some info := new.find? name | throw <| IO.userError s!"missing declaration {name}"
      if proof new info then
        if !isPrivateName name then checkStatement new ports name info.type
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
