import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Registry

namespace LeanInformationAudit.Tests.ReifierProviderBinding
open Lean Meta Elab Command
open LeanInformationAudit RegistrationReifier

private def expectFailure (label reason : String) (action : MetaM Unit) : MetaM Unit := do
  let outcome ← try action; pure none catch e => pure (some (← e.toMessageData.toString))
  let some actual := outcome | throwError "{label}: expected rejection"
  unless (actual.splitOn reason).length > 1 do throwError "{label}: {actual}"
  logInfo m!"P1_REJECTION {label} {actual}"
  logInfo m!"P1_NEGATIVE {label} {reason}"

-- The bridge supplies only metadata and uses the production diagnostic print options.
private def check (info : ConstantInfo) (owner : Name) : MetaM Unit := do
  match checkProviderPin info owner with
  | .ok _ => pure ()
  | .error message =>
    withOptions (fun o => (o.setBool `pp.universes true).setBool `pp.explicit true) do
      throwError message

private def changeOuterBinder : Expr → Expr
  | .forallE n t b bi => .forallE n t b (if bi == .default then .implicit else .default)
  | t => t

-- Change precisely the third binder: X and Y stay implicit, Fintype becomes implicit.
private def changeFintypeBinder : Expr → Except String Expr
  | .forallE x tx (.forallE y ty (.forallE f tf b .instImplicit) biy) bix =>
    if tf.isAppOfArity ``Fintype 1 then
      .ok (.forallE x tx (.forallE y ty (.forallE f tf b .implicit) biy) bix)
    else .error "interior binder is not Fintype"
  | _ => .error "interior binder is not instance implicit"

/-- Kernel acceptance is checked under a fresh fixture-owned Name in the current
context. Reflection reads that declaration back; only its Name is then rebound
for the pure pin decision. The proof value is never a checker input. -/
private def reflectedVariant (provider : Name) (label change : String) : MetaM ConstantInfo := do
  let .thmInfo info ← getConstInfo provider | throwError "pin control: not theorem"
  let fixture := (`P1Fixture).str ("impostor_" ++ label)
  let type ← if change == "raw_type" then pure (mkAnnotation `changedProviderType info.type)
    else if change == "binder" then pure (changeOuterBinder info.type)
    else if change == "interior_binder" then
      match changeFintypeBinder info.type with
      | .ok type => pure type
      | .error reason => throwError reason
    else pure info.type
  let levels := if change == "universe_order" then info.levelParams.reverse else info.levelParams
  let (levels, type, value) := if change == "universe_rename" then
    let renamed := levels.map (fun n => n.str "renamed")
    (renamed, type.instantiateLevelParams levels (renamed.map Level.param),
      info.value.instantiateLevelParams levels (renamed.map Level.param))
    else (levels, type, info.value)
  if change == "kind" then
    addDecl (.defnDecl {
      name := fixture, levelParams := levels, type, value, hints := .abbrev, safety := .safe })
  else addDecl (.thmDecl { name := fixture, levelParams := levels, type, value })
  let reflected ← getConstInfo fixture
  logInfo m!"P1_KERNEL_ACCEPTED {label} {fixture}"
  match reflected with
  | .thmInfo v => return .thmInfo { v with name := provider }
  | .defnInfo v => return .defnInfo { v with name := provider }
  | _ => throwError "unexpected fixture declaration kind"

private def providerIdentityProbe (suffix : String) (changeType : Bool) : MetaM Unit := do
  let name := providerModule.str suffix
  let label := "provider_" ++ (if changeType then "type_" else "module_") ++ suffix
  let info ← reflectedVariant name label (if changeType then "binder" else "same_module")
  expectFailure label
    ("P1.UnsupportedDescriptor: provider " ++ (if changeType then "type pin" else "module")) do
      check info `P1.ImpostorProvider
  -- Every identity arm also isolates ownership with the unchanged, reflected type.
  -- The type arm above retains its original diagnostic and precedence assertion.
  unless checkProviderPin (← getConstInfo name) `P1.ImpostorProvider matches .error _ do
    throwError "{label}: unchanged provider type lost module rejection"

private def providerPinProbe (name : Name) (change : String) : MetaM Unit := do
  let label := s!"provider_pin_{change}_{name.getString!}"
  let info ← reflectedVariant name label change
  if change == "same_module" || change == "universe_rename" then
    check info providerModule
    logInfo m!"P1_A5 {label} accepted"
  else
    expectFailure label (if change == "kind" then "provider is not a theorem" else "provider type pin") do
      check info providerModule

-- Foreign ownership is a reflected metadata input. Actual imported-module
-- resolution is exercised separately, using genuine imported constants.
private def providerForeignProbe (name : Name) : MetaM Unit := do
  let label := s!"provider_foreign_import_{name.getString!}"
  let info ← reflectedVariant name label "same_module"
  expectFailure label "provider module" do
    check info `P1ForeignProvider

run_meta do
  let saved ← getEnv
  try
    for changeType in #[true, false] do
      for suffix in #["pointwise", "sensitivity", "variation"] do
        providerIdentityProbe suffix changeType
    for name in #[pointwiseProvider, sensitivityProvider, variationProvider] do
      for change in #["same_module", "binder", "raw_type", "kind"] do
        providerPinProbe name change
    providerPinProbe variationProvider "universe_order"
    providerPinProbe variationProvider "universe_rename"
    for name in #[pointwiseProvider, sensitivityProvider, variationProvider] do
      providerForeignProbe name
    providerPinProbe pointwiseProvider "interior_binder"
  finally setEnv saved

-- A genuine current-module declaration has no imported owner.
private theorem currentDeclaration : True := True.intro

private def reflectionNatAdd : MetaM Unit := do
  let env ← getEnv
  let owner := declaringModuleOf env ``Nat.add
  unless owner == some `Init.Prelude do
    throwError "reflection_nat_add: expected Init.Prelude, got {owner}"
  -- Nat.add is outside the provider set, so changing the owner's argument alone
  -- cannot change checkedProvider Nat.add's unknown-provider outcome. Reflect
  -- the wrapper's declaration too: the specified bypass must remove this edge.
  -- This pins the implementation edge, not arbitrary semantic data flow.
  let some body := (← getConstInfo ``checkedProvider).value?
    | throwError "reflection_nat_add: missing checkedProvider body"
  unless (body.find? (·.isConstOf ``declaringModuleOf)).isSome do
    throwError "reflection_nat_add: checkedProvider bypassed declaringModuleOf"
  logInfo m!"P1_REFLECTION reflection_nat_add owner={owner} wrapper_dependency=present"

private def reflectionProvider (name : Name) : MetaM Unit := do
  let env ← getEnv
  unless declaringModuleOf env name == some providerModule do
    throwError "reflection_provider_{name.getString!}: incorrect owner"
  let info ← getConstInfo name
  let checked ← checkedProvider name
  unless info.name == checked.name && info.type.equal checked.type &&
      info.levelParams == checked.levelParams do
    throwError "reflection_provider_{name.getString!}: lookup changed metadata"
  logInfo m!"P1_REFLECTION reflection_provider_{name.getString!} lookup_and_wrapper accepted"

private def reflectionCurrent : MetaM Unit := do
  let env ← getEnv
  unless declaringModuleOf env ``currentDeclaration == none do
    throwError "reflection_current_module: expected no imported owner"
  let owner := (declaringModuleOf env ``currentDeclaration).getD env.header.mainModule
  unless owner == `LeanInformationAudit.Tests.RegistrationGates.ReifierProviderBinding do
    throwError "reflection_current_module: incorrect main module"
  unless declaringModuleOf env `P1Fixture.missing == none do
    throwError "reflection_current_module: missing declaration acquired owner"
  logInfo m!"P1_REFLECTION reflection_current_module none fallback={owner} missing=none"

run_meta do
  reflectionNatAdd
  for name in #[pointwiseProvider, sensitivityProvider, variationProvider] do
    reflectionProvider name
  reflectionCurrent

end LeanInformationAudit.Tests.ReifierProviderBinding
