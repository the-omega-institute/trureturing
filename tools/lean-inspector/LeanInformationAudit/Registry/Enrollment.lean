import LeanInformationAudit.Registry.Evidence
import LeanInformationAudit.TemplateEnrollment
import LeanInformationAudit.CompiledAxioms

namespace LeanInformationAudit.TemplateAudit
open Lean Meta Elab Command

private initialize templateIndexExt : EnvExtension TemplateIndex ←
  registerEnvExtension (pure {})

def resetTemplatePlans (env : Environment) : Environment := templateIndexExt.setState env {}

/-- Read-only observation of actual query operations in the environment's
current assessment index. The observer cannot supply a plan or affect admission. -/
def observeSelectedPlan [Monad m] (env : Environment) (name : Name)
    (observe : m Unit) : m (Except String TemplatePlanData) :=
  (templateIndexExt.getState env).lookup name observe

/-- Plans are rebuilt from recorded author inputs by the current evaluator. -/
def selectedPlan (env : Environment) (name : Name) : Except String TemplatePlanData :=
  observeSelectedPlan env name (pure () : Id Unit)

/-- Assessed plan size, including keys, within the current fixed quota. -/
def assessedPlanBytes (env : Environment) : Nat := (templateIndexExt.getState env).bytes

private initialize primitivePins : SimplePersistentEnvExtension PrimitivePin (Array PrimitivePin) ←
  registerSimplePersistentEnvExtension {
    name := `LeanInformationAudit.TemplateAudit.primitivePins
    addEntryFn := Array.push
    addImportedFn := fun modules => modules.foldl (· ++ ·) #[] }

private def ownerOf (env : Environment) (name : Name) : Option Name :=
  if env.contains name then
    some ((RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule)
  else none

private def runCompiled (action : ReaderT CompiledEnrollment.Context IO α) : MetaM α := do
  let env ← getEnv
  let locals ← getLCtx
  let options ← getOptions
  let heartbeatStart ← getInitHeartbeats
  let heartbeatLimit ← getMaxHeartbeats
  let mut registeredTheorems : NameSet := {}
  for entry in InformationRegistry.entries env do
    registeredTheorems := registeredTheorems.insert entry.theoremName
  let axioms ← IO.mkRef ({} : CompiledAxioms.AxiomClosureState)
  RegistrationGates.Compiler.runQuery (fun provenance => do
    let provenance := { provenance with
      view := { provenance.view with ownerOf := ownerOf env }
      options, heartbeatStart, heartbeatLimit }
    let context : CompiledEnrollment.Context := {
      provenance
      moduleIndex? := fun name => (env.getModuleIdx? name).map (·.toNat)
      moduleImports? := fun name => (env.getModuleIdx? name).bind fun index =>
        env.header.moduleData[index.toNat]?.map (·.imports.map (·.module))
      pins := primitivePins.getState env
      recursive := fun name => recExt.isTagged env name
      registeredTheorems
      implementedBy := fun name => (Compiler.getImplementedBy? env name).isSome
      extern := fun name => (getExternAttrData? env name).isSome
      collectAxioms := CompiledAxioms.collectAxiomsShared env.find? axioms }
    action.run context) locals

def initializeGrammarPins : CommandElabM Unit := do
  unless (← getEnv).header.mainModule == `LeanInformationAudit.Registry do
    throwError "incomplete_closure:E2.pin_producer_owner"
  for name in CompiledEnrollment.standardDictionaryNames do
    if let some info := (← getEnv).find? name then
      let some owner := ownerOf (← getEnv) name | throwError "DTR primitive owner missing"
      let .ok (typeId, _) ← liftTermElabM <| rawIdentity info.levelParams info.type
        | throwError "DTR primitive type exceeds identity bound: {name}"
      let .ok (bodyId, _) ← liftTermElabM <| rawIdentity info.levelParams (info.value?.getD info.type)
        | throwError "DTR primitive body exceeds identity bound: {name}"
      modifyEnv fun env => primitivePins.addEntry env {
        identity := { name, owner, typeIdentity := typeId, bodyIdentity := bodyId }
        levelCount := info.levelParams.length }

def diagnosticFields (message : String) : String :=
  match message.splitOn ":" with
  | reason :: rule :: site =>
    "reason=" ++ reason ++ " rule=" ++ rule ++ " site=" ++
      (Json.str (String.intercalate ":" site)).compress
  | _ => "reason=incomplete_closure rule=E8.exception site=" ++ (Json.str message).compress

/-- Nested Meta boundaries may use their own initial heartbeat count. The
outer boundary still settles all elapsed work, including the final subcall. -/
def withCumulativeBudget (action : MetaM α) : MetaM α :=
  withCurrHeartbeats <| withOptions (fun options =>
    let configured := maxHeartbeats.get options
    options.set `maxHeartbeats (if configured == 0 then 100000 else min 100000 configured)) do
    let limit := Core.getMaxHeartbeats (← getOptions)
    -- withOptions changes options/maxRecDepth, not Core's heartbeat field.
    controlAt CoreM fun runInBase => withReader (fun context : Core.Context =>
      { context with maxHeartbeats :=
          if context.maxHeartbeats == 0 then limit else min limit context.maxHeartbeats }) do
      let result ← runInBase action
      Core.checkMaxHeartbeats "template cumulative budget"
      return result

def exceptionDiagnostic (error : Exception) : MetaM String := do
  if error.isMaxHeartbeat then return "incomplete_closure:E8.heartbeats"
  if error.isMaxRecDepth then return "incomplete_closure:E8.recursion_depth"
  return ← error.toMessageData.toString

/-- Unsupported enrollment leaves no assessed plan. All budgets are lower-only. -/
def enroll (rootId : Name) (options : Options) (name : Name)
    (constructors : Array Name := #[]) : CommandElabM (Except String Unit) :=
  withScope (fun scope => { scope with opts := options }) do
    let saved ← getEnv
    let answer ← liftTermElabM <| tryCatchRuntimeEx
      (withCumulativeBudget do
        let checkedPlan ← runCompiled (CompiledEnrollment.compileTemplate rootId name constructors)
        let env ← getEnv
        let policyOwners := #[`LeanInformationAudit.RegistryTypes, `LeanInformationAudit.Registry,
          `LeanInformationAudit.ReadoutProvenance, `LeanInformationAudit.Registry.Enrollment]
          |>.filter (fun name => (env.getModuleIdx? name).isSome)
        NativeCoherence.validate
          (#[rootId] ++ policyOwners ++ checkedPlan.data.dependencies.map (·.owner))
        let current := templateIndexExt.getState (← getEnv)
        match current.lookup name (pure () : Id Unit) with
        | .ok _ => throwError "unclassified_form:E7.duplicate_enrollment"
        | .error _ => pure ()
        if let some error := current.error then throwError error
        if current.bytes + checkedPlan.retainedBytes > 8388608 then
          throwError "incomplete_closure:E8.import_bytes"
        modifyEnv fun env => templateIndexExt.modifyState env fun index =>
          index.insertChecked checkedPlan
        pure (.ok ()))
      (fun error => do
        let message ← exceptionDiagnostic error
        pure (.error (if message.startsWith "unclassified_form:" ||
            message.startsWith "forbidden_dependency:" || message.startsWith "incomplete_closure:"
          then message else "incomplete_closure:E8.elaboration:" ++ message)))
    if answer matches .error _ then setEnv saved
    return answer

def typePositions := CompiledEnrollment.typePositions

def checkArguments (theoremName : Name) (arguments : Array Expr) (available : Nat)
    (constructors : Array Name := #[]) (indices : Array Bool := #[]) : MetaM (Array Name × Nat) :=
  runCompiled (CompiledEnrollment.checkArguments theoremName arguments available constructors indices)

def checkExtractionType (theoremName : Name) (type : Expr) (available : Nat)
    (constructors : Array Name := #[]) : MetaM (Array DependencyIdentity × Nat) :=
  runCompiled (CompiledEnrollment.checkExtractionType theoremName type available constructors)

def checkIndependentInputCarrier (theoremName : Name) (type : Expr) (available : Nat) : MetaM Bool :=
  runCompiled (CompiledEnrollment.checkIndependentInputCarrier theoremName type available)

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.RegistrationGates
open Lean

/-- Current declared argument entry, shared with enrollment's finite grammar. -/
def templateArgumentsCurrent (theoremName : Name) (arguments : Array Expr)
    (availableWork : Nat) (constructors : Array Name := #[]) (indices : Array Bool := #[]) :
    CoreM (Except String (Array Name × Nat)) :=
  Meta.MetaM.run' <| tryCatchRuntimeEx
    (TemplateAudit.withCumulativeBudget <| .ok <$> TemplateAudit.checkArguments
      theoremName arguments availableWork constructors indices)
    (fun error => do
      let message ← TemplateAudit.exceptionDiagnostic error
      return .error (if message.startsWith "unclassified_form:" ||
          message.startsWith "forbidden_dependency:" || message.startsWith "incomplete_closure:"
        then message else "incomplete_closure:E8.argument_elaboration:" ++ message))

end LeanInformationAudit.RegistrationGates

