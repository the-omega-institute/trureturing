import LeanInformationAudit.Registry.SourceContract
import LeanInformationAudit.CompiledAssessment

namespace LeanInformationAudit.TemplateBinding
open Lean Meta TemplateAudit

def dependencyJson := CompiledAssessment.dependencyJson
def missingDeclarationDiagnostic := CompiledAssessment.missingDeclarationDiagnostic
private def diagnosticMessage := CompiledAssessment.diagnosticMessage

private initialize assessmentEvents : EnvExtension (Array TemplateOccurrenceKey) ←
  registerEnvExtension (pure #[])

/-- Read-only observations of actual occurrence assessments in this environment. -/
def observedAssessments (env : Environment) : Array TemplateOccurrenceKey :=
  assessmentEvents.getState env

/-- Registration and final joined assessment share this function. Failure of a
new binding check is retained metadata, never a module elaboration failure. -/
private def assessUncached (event : TemplateOccurrenceEvent) (claim : Option TemplateBindingClaim) : MetaM BindingRecord := do
  modifyEnv fun env => assessmentEvents.modifyState env (·.push event.key)
  match claim with
  | none => return {
      occurrence := event, descriptor := none, bindingOwner := none, result := .undeclared
      escape := { bridgeKind := (← bridgeKind event) } }
  | some claim =>
    let plans := currentTemplateIndex (← getEnv)
    let record ← withCumulativeBudget <| runCompiled fun enrollment =>
      (CompiledAssessment.assess event (some claim)).run { enrollment, plans }
    if let .declaredValidated certificate := record.result then
      let some descriptor := claim.descriptor | return record
      let .const name _ := descriptor.getAppFn | return record
      let .ok plan := selectedPlan (← getEnv) name | return record
      NativeCoherence.validate (#[plan.definitionOwner, plan.enrollmentOwner,
        event.key.registrationModule, claim.owner] ++
        (plan.dependencies ++ certificate.argumentInputs ++ certificate.extractionInputs).map (·.owner))
    return record
private abbrev CacheSemantics := Bool × ReducibilityStatus × Option Name × Bool ×
  Option (Name × Nat × Nat × Bool)

private def cacheSemantics (env : Environment) (name : Name) : CacheSemantics :=
  (Lean.isClass env name, getReducibilityStatusCore env name,
    Compiler.getImplementedBy? env name, (getExternAttrData? env name).isSome,
    (env.getProjectionFnInfo? name).map fun p => (p.ctorName, p.numParams, p.i, p.fromClass))

/-- An immutable occurrence result and the exact inputs it consumed. This cache
is local to an Environment and is never serialized as certification authority. -/
private structure CachedAssessment where
  record : BindingRecord
  claim : TemplateBindingClaim
  options : Options
  registry : Array InformationRegistryEntry
  planName : Name
  planIdentity : String
  constants : Array (Name × ConstantInfo × Name × CacheSemantics)

private initialize assessmentCache : EnvExtension (Std.HashMap TemplateOccurrenceKey CachedAssessment) ←
  registerEnvExtension (pure {})

private def sameCacheObject (a b : α) : Bool := unsafe ptrEq a b

private def sameCacheEvent (a b : TemplateOccurrenceEvent) : Bool :=
  a.key == b.key && a.unitName == b.unitName && a.realizationName == b.realizationName &&
  a.statement.equal b.statement && a.levelParams == b.levelParams &&
  a.statementIdentity == b.statementIdentity && a.arena.equal b.arena &&
  a.registrationSource == b.registrationSource &&
  a.registrationSourceIdentity == b.registrationSourceIdentity

private def sameCacheClaim (a b : TemplateBindingClaim) : MetaM Bool := do
  let descriptorsMatch ← match a.descriptor, b.descriptor with
    | none, none => pure true
    | some a, some b =>
      let (a, _) ← eraseProofs a
      let (b, _) ← eraseProofs b
      pure (a.equal b)
    | _, _ => pure false
  return a.key == b.key && a.owner == b.owner && a.arena.equal b.arena &&
  a.resolutionDiagnostic == b.resolutionDiagnostic && a.escapeInput == b.escapeInput && descriptorsMatch

private def cacheCurrent (cached : CachedAssessment) (event : TemplateOccurrenceEvent)
    (claim : TemplateBindingClaim) : MetaM Bool := do
  unless sameCacheEvent cached.record.occurrence event do return false
  -- An ill-formed claim cannot reuse a retained result; the uncached assessment
  -- reports its own diagnostic.
  unless ← (try sameCacheClaim cached.claim claim catch _ => pure false) do return false
  let env ← getEnv
  unless sameCacheObject cached.options (← getOptions) &&
      sameCacheObject cached.registry (InformationRegistry.entries env) do return false
  let .ok plan := selectedPlan env cached.planName | return false
  unless plan.planIdentity == cached.planIdentity do return false
  for (name, info, owner, semantics) in cached.constants do
    let some current := env.find? name | return false
    unless sameCacheObject info current && cacheSemantics env name == semantics &&
        (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule == owner do
      return false
  try
    NativeCoherence.validate (#[claim.owner, event.key.registrationModule] ++
      cached.constants.map (fun (_, _, owner, _) => owner))
    return true
  catch _ => return false

private def retainAssessment (record : BindingRecord) (claim : TemplateBindingClaim)
    (certificate : TemplateBindingCertificate) : MetaM Unit := do
  if certificate.sourceBinding.isSome then return
  let some descriptor := claim.descriptor | return
  let .const name _ := descriptor.getAppFn | return
  let env ← getEnv
  let .ok plan := selectedPlan env name | return
  let mut names : NameSet := {}
  for name in ← inspectionDependencies record.occurrence do names := names.insert name
  for value in claim.escapeInput.fromObject.toArray ++ claim.escapeInput.continuation.toArray do
    for name in value.getUsedConstants do names := names.insert name
  if let some residual := record.escape.continuation then
    if let some chain := residual.chainName then names := names.insert chain
  for dependency in plan.dependencies ++ certificate.argumentInputs ++ certificate.extractionInputs do
    names := names.insert dependency.name
  for name in #[plan.name, record.occurrence.key.theoremName, record.occurrence.unitName,
      record.occurrence.realizationName, record.occurrence.key.objectArena] do
    names := names.insert name
  let mut constants := #[]
  for name in names do
    let info ← getConstInfo name
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    constants := constants.push (name, info, owner, cacheSemantics env name)
  let cached : CachedAssessment := {
    record, claim, constants, options := ← getOptions,
    registry := InformationRegistry.entries env, planName := name, planIdentity := plan.planIdentity }
  modifyEnv fun env => assessmentCache.modifyState env (·.insert record.occurrence.key cached)

/-- Every caller uses the same assessment. A hit requires exact occurrence,
claim, selected plan, options and native dependencies.
The authoritative caller still validates the complete native join first. -/
def assess (event : TemplateOccurrenceEvent) (claim : Option TemplateBindingClaim) : MetaM BindingRecord := do
  if let some claim := claim then
    if let some cached := (assessmentCache.getState (← getEnv))[event.key]? then
      if ← cacheCurrent cached event claim then return cached.record
  let record ← assessUncached event claim
  if let (some claim, .declaredValidated certificate) := (claim, record.result) then
    try
      retainAssessment record claim certificate
    catch error =>
      let diagnostic := diagnosticMessage event.key
        ("incomplete_closure:dtr.cache_inputs:" ++ (← exceptionDiagnostic error)) Json.null
      return { record with result := .declaredUnresolved diagnostic }
  return record


end LeanInformationAudit.TemplateBinding
