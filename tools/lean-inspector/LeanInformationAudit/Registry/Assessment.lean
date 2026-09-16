import LeanInformationAudit.Registry.Enrollment

namespace LeanInformationAudit.TemplateBinding
open Lean Meta TemplateAudit

private structure CompareState where
  remaining : Nat
  extractionNames : NameSet := {}
  constructorTypes : Array Name := #[]

private abbrev CompareM := StateT CompareState MetaM
private def debit (n : Nat := 1) : CompareM Unit := do
  Core.checkMaxHeartbeats "template comparison"
  unless n ≤ (← get).remaining do throwError "incomplete_closure:E8.comparison_work"
  modify fun state => { state with remaining := state.remaining - n }

private def construct (action : Nat → Except String (α × Nat)) : CompareM α := do
  let (result, work) ← match action (← get).remaining with
    | .ok value => pure value
    | .error reason => throwError reason
  debit work
  return result

private def materialize (plan : PlanNode) : CompareM Expr :=
  construct (fun fuel => PlanTransform.toExpr plan fuel)

private partial def alpha (e : Expr) (depth : Nat := 0) : CompareM Expr := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.comparison_depth"
  let child := fun x => alpha x (depth + 1)
  match e with
  | .app f a => return .app (← child f) (← child a)
  | .lam _ t b bi => return .lam .anonymous (← child t) (← child b) bi
  | .forallE _ t b bi => return .forallE .anonymous (← child t) (← child b) bi
  | .letE _ t v b nd => return .letE .anonymous (← child t) (← child v) (← child b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ | .fvar _ => throwError "incomplete_closure:dtr.open_comparison"
  | _ => return e

private def equalRaw (a b : Expr) : CompareM Bool := do
  return (← alpha a).equal (← alpha b)

private def rawSubstitute (body argument : Expr) (cutoff : Nat) : CompareM Expr :=
  construct (fun fuel => PlanTransform.substituteExpr body argument cutoff fuel)

private def substitute (body argument : PlanNode) : CompareM PlanNode :=
  construct (fun fuel => PlanTransform.substitutePlan body argument fuel)

private def levels (params : List Name) (values : List Level) (plan : PlanNode) : CompareM PlanNode :=
  construct (fun fuel => PlanTransform.instantiatePlan plan params values fuel)

private partial def applyPlan (plan : PlanNode) (arg : PlanNode) : CompareM PlanNode := do
  debit
  match plan with
  | .expanded _ body | .typeNode body => applyPlan body arg
  | .audit input body => return .audit input (← applyPlan body arg)
  | .lam domain body _ => return .audit (.typeNode domain) (← substitute body arg)
  | _ => throwError "unclassified_form:dtr.unsaturated_plan"

private def isRealizationType (type : Expr) : Bool :=
  #[`D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
    `LeanInformationAudit.StructuralPrimitiveRealization].contains (type.getAppFn.constName?.getD .anonymous)

/-- Expose only a saturated forwarding spine. The parameter vector must contain
every lambda variable exactly once, in its original order, as a whole argument.
No beta reduction is performed inside an actual supplied argument. -/
private def forwardActual (theoremName selected : Name) (initial : Expr) : CompareM Expr := do
  let mut actual := initial
  let mut visited : NameSet := {}
  for _ in [:256] do
    debit
    let .const name universeArgs := actual.getAppFn | return actual
    if name == selected then return actual
    let some (.defnInfo info) := (← getEnv).find? name | return actual
    unless isRealizationType info.type.getForallBody do return actual
    if visited.contains name || info.safety != .safe ||
        (← isRecursiveDefinition name) || info.all.length > 1 ||
        ((← getEnv).getProjectionFnInfo? name).isSome ||
        (Compiler.getImplementedBy? (← getEnv) name).isSome ||
        (getExternAttrData? (← getEnv) name).isSome then
      throwError "unclassified_form:dtr.extraction_kind"
    let arguments := actual.getAppArgs
    if actual.hasFVar || actual.hasLooseBVars || actual.hasMVar ||
        universeArgs.length != info.levelParams.length then
      throwError "incomplete_closure:dtr.extraction_open"
    let mut body := info.value
    let mut arity := 0
    while let .lam _ _ tail _ := body do
      debit
      arity := arity + 1
      body := tail
    unless body.getAppFn.isConst && arity == arguments.size do return actual
    let mut forwarded : Array Nat := #[]
    for argument in body.getAppArgs do
      debit
      if argument.hasLooseBVars then
        let .bvar index := argument | return actual
        forwarded := forwarded.push index
    unless forwarded == (List.range arity).reverse.toArray do return actual
    let (dependencies, typeWork) ← checkExtractionType info.type (← get).remaining (← get).constructorTypes
    debit typeWork
    let indices := indexPositions info.type
    debit indices.size
    let (argumentNames, argumentWork) ← match ←
        RegistrationGates.templateArgumentsCurrent theoremName arguments (← get).remaining
          (← get).constructorTypes indices with
      | .ok result => pure result
      | .error diagnostic => throwError diagnostic
    debit argumentWork
    let names := dependencies.map (·.name) ++ argumentNames
    modify fun state =>
      let extracted := names.foldl (fun found n => found.insert n)
        (state.extractionNames.insert name)
      { state with extractionNames := extracted }
    let .ok (_, bodyWork) := rawIdentity info.levelParams info.value (← get).remaining
      | throwError "incomplete_closure:E8.extraction_body"
    debit bodyWork
    let mut value ← construct (fun fuel => PlanTransform.instantiateExpr info.value info.levelParams universeArgs fuel)
    for argument in arguments do
      let .lam _ _ tail _ := value | throwError "incomplete_closure:dtr.extraction_telescope"
      value ← rawSubstitute tail argument 0
    visited := visited.insert name
    actual := value
  throwError "incomplete_closure:E8.extraction_depth"

private def planSpine (plan : PlanNode) : PlanNode × Array PlanNode := Id.run do
  let mut head := plan
  let mut arguments := #[]
  while let .app f a := head do
    head := f
    arguments := arguments.push a
  return (head, arguments.reverse)

/-- Only checked template lambda sites have administrative beta reduction.
Arguments and constructor fields keep their original nodes and origins. -/
private partial def checkedHead (plan : PlanNode) (depth : Nat := 0) : CompareM PlanNode := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.extraction_depth"
  match plan with
  | .expanded _ body | .typeNode body | .audit _ body => checkedHead body (depth + 1)
  | .app f a =>
    let f ← checkedHead f (depth + 1)
    match f with
    | .lam _ body _ => checkedHead (← substitute body a) (depth + 1)
    | _ => return .app f a
  | _ => return plan

mutual
/-- Read already checked type/proof-leaf nodes after slot substitution. Plan
lambda applications expose their instantiated obligations; supplied nodes are
never inspected or normalized by this consumer. -/
private partial def retainedTypes (plan : PlanNode) (context : Array Expr := #[])
    (depth : Nat := 0) : CompareM (Array (Expr × Array Expr)) := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.type_obligation_depth"
  let child := fun p => retainedTypes p context (depth + 1)
  let obligation := fun type : Expr => (type, if type.hasLooseBVars then context else #[])
  match plan with
  | .atom _ | .supplied _ => return #[]
  | .proofLeaf type _ => return #[obligation type]
  | .typeNode checked => return #[obligation (← materialize checked)] ++ (← child checked)
  | .expanded _ checked => child checked
  | .audit input body => return (← child input) ++ (← child body)
  | .app f a =>
    let (head, pending) ← retainedHead f context (depth + 1)
    if let .lam domain body _ := head then
      return pending ++ #[obligation (← materialize domain)] ++ (← child domain) ++
        (← child a) ++ (← child (← substitute body a))
    return pending ++ (← child head) ++ (← child a)
  | .lam domain body bi | .forallE domain body bi =>
    let type ← materialize domain
    let binder := Expr.forallE .anonymous type (.bvar 0) bi
    return #[obligation type] ++ (← child domain) ++
      (← retainedTypes body (context.push binder) (depth + 1))
  | .letE type value body _ =>
    -- Substitution here discharges dependent type obligations only. The
    -- comparator still retains the original let/value/body without zeta.
    return #[obligation (← materialize type)] ++ (← child type) ++ (← child value) ++
      (← child (← substitute body value))
  | .mdata _ body | .proj _ _ body => child body

/-- Expose a plan-created lambda while retaining obligations from every
intermediate application. Do not inspect an uninstantiated lambda body or
normalize a supplied node to discover a function head. -/
private partial def retainedHead (plan : PlanNode) (context : Array Expr)
    (depth : Nat) : CompareM (PlanNode × Array (Expr × Array Expr)) := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.type_obligation_depth"
  let child := fun p => retainedHead p context (depth + 1)
  let types := fun p => retainedTypes p context (depth + 1)
  let obligation := fun type : Expr => (type, if type.hasLooseBVars then context else #[])
  match plan with
  | .expanded _ body => child body
  | .audit input body =>
    let pending ← types input
    let (head, rest) ← child body
    return (head, pending ++ rest)
  | .typeNode checked =>
    let (head, rest) ← child checked
    return (head, #[obligation (← materialize checked)] ++ rest)
  | .app f a =>
    let (head, pending) ← child f
    if let .lam domain body _ := head then
      let inputs := #[obligation (← materialize domain)] ++ (← types domain) ++ (← types a)
      let (result, rest) ← child (← substitute body a)
      return (result, pending ++ inputs ++ rest)
    return (.app head a, pending)
  | _ => return (plan, #[])
end

private structure MatchContext where
  theoremName : Name
  selected : Name
  descriptor : Expr
  body : PlanNode

private structure FixedProjection where
  typeName : Name
  index : Nat
  base : Expr
  parameters : Array Expr := #[]
  universeArgs : Option (List Level) := none

private def fixedProjection (actual : Expr) : MetaM (Option FixedProjection) := do
  match actual with
  | .proj typeName index base => return some { typeName, index, base }
  | _ =>
    let .const name universeArgs := actual.getAppFn | return none
    let some projection := (← getEnv).getProjectionFnInfo? name | return none
    let arguments := actual.getAppArgs
    unless arguments.size == projection.numParams + 1 do return none
    return some {
      typeName := projection.ctorName.getPrefix
      index := projection.i
      base := arguments[projection.numParams]!
      parameters := arguments.extract 0 projection.numParams
      universeArgs := some universeArgs }

private def realizationInterfaces : Array Name := #[
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
  `LeanInformationAudit.StructuralPrimitiveRealization]

private partial def matchesPlan (context : MatchContext) (plan : PlanNode) (actual : Expr)
    (depth : Nat := 0) : CompareM Bool := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.match_depth"
  let child := fun p e => matchesPlan context p e (depth + 1)
  -- A supplied argument is an immutable comparison leaf. In particular, an
  -- apparent projection or forwarding application inside it is not reduced.
  if let .typeNode checked := plan then return ← child checked actual
  if let .audit _ checked := plan then return ← child checked actual
  if let .supplied raw := plan then return ← equalRaw raw actual
  if let some projection ← fixedProjection actual then
    if realizationInterfaces.contains projection.typeName then
      let base ← forwardActual context.theoremName context.selected projection.base
      if ← equalRaw base context.descriptor then
        let record ← checkedHead context.body
        let (head, fields) := planSpine record
        if let .atom (.const ctor universeArgs) := head then
          if let some (.ctorInfo info) := (← getEnv).find? ctor then
            if info.induct == projection.typeName && info.numParams + projection.index < fields.size &&
                (projection.parameters.isEmpty || projection.parameters.size == info.numParams) &&
                (projection.universeArgs.isNone || projection.universeArgs == some universeArgs) then
              let mut parametersMatch := true
              for i in [:projection.parameters.size] do
                unless ← child fields[i]! projection.parameters[i]! do parametersMatch := false
              if parametersMatch then
                return ← child plan (← materialize fields[info.numParams + projection.index]!)
      else if let .const ctor universeArgs := base.getAppFn then
        if let some (.ctorInfo info) := (← getEnv).find? ctor then
          let fields := base.getAppArgs
          if info.induct == projection.typeName && fields.size == info.numParams + info.numFields &&
              projection.index < info.numFields &&
              (projection.parameters.isEmpty || projection.parameters.size == info.numParams) &&
              (projection.universeArgs.isNone || projection.universeArgs == some universeArgs) then
            -- Audit the entire literal receiver before selecting a field. An
            -- unused anchor or signature parameter is still an extraction input.
            let indices := indexPositions info.type
            debit (indices.size + projection.parameters.size)
            let (names, work) ← match ← RegistrationGates.templateArgumentsCurrent
                context.theoremName (fields ++ projection.parameters) (← get).remaining
                (← get).constructorTypes (indices ++ indices.extract 0 projection.parameters.size) with
              | .ok result => pure result
              | .error diagnostic => throwError diagnostic
            debit work
            modify fun state =>
              let extracted := names.foldl (fun found name => found.insert name)
                (state.extractionNames.insert ctor)
              { state with extractionNames := extracted }
            let mut parametersMatch := true
            for i in [:projection.parameters.size] do
              unless ← equalRaw fields[i]! projection.parameters[i]! do parametersMatch := false
            if parametersMatch then return ← child plan fields[info.numParams + projection.index]!
  match plan with
  | .typeNode checked => child checked actual
  | .audit _ checked => child checked actual
  | .expanded raw body =>
    if ← equalRaw raw actual then return true
    child body actual
  | .atom raw | .supplied raw | .proofLeaf _ raw => equalRaw raw actual
  | .app (.lam _ body _) arg => child (← substitute body arg) actual
  | .app f a =>
    match actual with
    | .app g b => return (← child f g) && (← child a b)
    | _ => return false
  | .lam t b bi =>
    match actual with
    | .lam _ u c bj => return bi == bj && (← child t u) && (← child b c)
    | _ => return false
  | .forallE t b bi =>
    match actual with
    | .forallE _ u c bj => return bi == bj && (← child t u) && (← child b c)
    | _ => return false
  | .letE t v b nd =>
    match actual with
    | .letE _ u w c ne => return nd == ne && (← child t u) && (← child v w) && (← child b c)
    | _ => return false
  | .mdata m b =>
    match actual with
    | .mdata n c => return (Expr.mdata m (.bvar 0)).equal (.mdata n (.bvar 0)) && (← child b c)
    | _ => return false
  | .proj n i b =>
    match actual with
    | .proj k j c => return n == k && i == j && (← child b c)
    | _ => return false

private def extract (event : TemplateOccurrenceEvent) : CompareM Expr := do
  debit
  let name := event.realizationName
  let info ← getConstInfo name
  let raw ← if info.type.isAppOfArity
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 then
    pure info.type.getAppArgs[2]!
  else if isRealizationType info.type then
    match info with
    | .defnInfo defn =>
      if defn.safety != .safe || (← isRecursiveDefinition name) || defn.all.length > 1 ||
          (Compiler.getImplementedBy? (← getEnv) name).isSome ||
          (getExternAttrData? (← getEnv) name).isSome then
        throwError "unclassified_form:dtr.extraction_kind"
      pure defn.value
    | _ => throwError "unclassified_form:dtr.extraction_kind"
  else throwError "unclassified_form:dtr.extraction_interface"
  -- The named realization is used at the occurrence's rigid universe telescope.
  -- Renaming its binders is permitted; permutation or arity guessing is not.
  if info.levelParams.isEmpty then return raw
  unless info.levelParams.length == event.levelParams.length do
    throwError "unclassified_form:dtr.extraction_universes"
  construct fun fuel => PlanTransform.instantiateExpr raw info.levelParams
    (event.levelParams.map Level.param) fuel

private def closed (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "incomplete_closure:dtr.descriptor_open"

private def inputIdentity (name : Name) : CompareM DependencyIdentity := do
  debit
  let info ← getConstInfo name
  let owner := (RegistrationReifier.declaringModuleOf (← getEnv) name).getD (← getEnv).header.mainModule
  let .ok (typeIdentity, typeWork) := TemplateAudit.rawIdentity info.levelParams info.type (← get).remaining
    | throwError "incomplete_closure:dtr.input_identity"
  debit typeWork
  -- A proof input retains its raw occurrence and full type identity. Its
  -- implementation is outside the provenance/evidence boundary.
  let bodyIdentity ← if ← isProp info.type then pure "" else match info.value? with
    | none => pure ""
    | some value =>
      let .ok (identity, bodyWork) := TemplateAudit.rawIdentity info.levelParams value (← get).remaining
        | throwError "incomplete_closure:dtr.input_identity"
      debit bodyWork
      pure identity
  return { name, owner, typeIdentity, bodyIdentity }

def dependencyJson (input : TemplateAudit.DependencyIdentity) : Json := Json.mkObj [
  ("name", toJson input.name.toString), ("owner", toJson input.owner.toString),
  ("type_identity", toJson input.typeIdentity), ("body_identity", toJson input.bodyIdentity)]

private def failureSite (reason : String) : String :=
  String.intercalate ":" ((reason.splitOn ":").drop 2)

private def failureRule (reason : String) : String :=
  (reason.splitOn ":")[1]?.getD "E8.exception"

private def diagnosticMessage (key : TemplateOccurrenceKey) (reason : String)
    (provenance : Json) : String :=
  s!"IE-C050 ClosedTruthReadout key={key.root}/{key.catalog}/{key.theoremName} " ++
    TemplateAudit.diagnosticFields reason ++ " readout=" ++ (toJson (failureSite reason)).compress ++
    " provenance=" ++ provenance.compress

/-- No descriptor means no supplied argument or extraction audit inputs. This
diagnostic records the missing declaration and grants no provenance certificate. -/
def missingDeclarationDiagnostic (key : TemplateOccurrenceKey) : String :=
  diagnosticMessage key "unclassified_form:dtr.missing_declaration" <| Json.mkObj [
    ("argument_inputs", Json.arr #[]), ("extraction_inputs", Json.arr #[]),
    ("plan_identity", Json.null), ("rule", toJson "dtr.missing_declaration"),
    ("site", toJson ""), ("template_key", Json.null)]

/-- Failure provenance names the raw supplied input roots and the native
extraction declaration. These identities describe the failing inputs, not an
admitted closure. A missing identity or exhausted diagnostic walk yields null.
The selected template's executable body is never scanned for this diagnostic. -/
private def diagnosticProvenance (event : TemplateOccurrenceEvent)
    (claim : TemplateBindingClaim) (reason : String) : MetaM Json := do
  if reason.startsWith "incomplete_closure:" then return Json.null
  try
    let env ← getEnv
    let descriptor := claim.descriptor
    let name := descriptor.bind fun e => e.getAppFn.constName?
    let plan := name.bind fun name => (selectedPlan env name).toOption
    let action : CompareM Json := do
      let mut names : NameSet := {}
      for argument in descriptor.map Expr.getAppArgs |>.getD #[] do
        for name in argument.getUsedConstants do names := names.insert name
      let arguments ← (names.toArray.qsort Name.quickLt).mapM inputIdentity
      let extraction ← inputIdentity event.realizationName
      return Json.mkObj [
        ("argument_inputs", Json.arr (arguments.map dependencyJson)),
        ("extraction_inputs", Json.arr #[dependencyJson extraction]),
        ("plan_identity", plan.map (toJson ∘ TemplatePlanData.planIdentity) |>.getD Json.null),
        ("rule", toJson (failureRule reason)), ("site", toJson (failureSite reason)),
        ("template_key", name.map (toJson ∘ Name.toString) |>.getD Json.null)]
    let (provenance, _) ← withCumulativeBudget <| action.run {
      remaining := min 524288 (TemplateAudit.informationTemplate.work.get (← getOptions)) }
    return provenance
  catch _ => return Json.null

private def validate (event : TemplateOccurrenceEvent) (descriptor : Expr)
    (bindingOwner : Name) : MetaM TemplateBindingCertificate := do
  closed descriptor
  let .const name universeArgs := descriptor.getAppFn
    | throwError "unclassified_form:dtr.descriptor_head"
  let plan ← match selectedPlan (← getEnv) name with
    | .ok plan => pure plan
    | .error reason => throwError reason
  let env ← getEnv
  validateSourceInputs plan.sourceInputs
  unless env.contains name do throwError "incomplete_closure:dtr.template_owner"
  let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
  unless owner == plan.definitionOwner && universeArgs.length == plan.levelParams.length &&
      descriptor.getAppArgs.size == plan.slots.size do
    throwError "unclassified_form:dtr.descriptor_telescope"
  let arguments := descriptor.getAppArgs
  let budget := min 524288 (TemplateAudit.informationTemplate.work.get (← getOptions))
  let (argumentNames, argumentWork) ← match ← RegistrationGates.templateArgumentsCurrent event.key.theoremName arguments budget plan.constructorTypes
      (plan.slots.map fun slot => slot.type.isConstOf ``Nat) with
    | .ok result => pure result
    | .error reason => throwError reason
  let compare : CompareM TemplateBindingCertificate := do
    debit plan.serializedBytes
    let actual ← extract event
    closed actual
    let mut body ← levels plan.levelParams universeArgs plan.plan
    let mut type ← levels plan.levelParams universeArgs plan.typePlan
    let mut obligations : Array (Expr × Array Expr) := #[]
    for argument in arguments do
      body ← applyPlan body (.supplied argument)
      match ← checkedHead type with
      | .forallE domain tail _ =>
        obligations := obligations.push ((← materialize domain), #[])
        obligations := obligations ++ (← retainedTypes domain)
        type ← substitute tail (.supplied argument)
      | _ => throwError "unclassified_form:dtr.descriptor_telescope"
    obligations := obligations.push ((← materialize type), #[])
    obligations := obligations ++ (← retainedTypes type) ++ (← retainedTypes body)
    let typeWork ← match ← RegistrationGates.templateTypesCurrent event.key.theoremName
        obligations (← get).remaining with
      | .ok work => pure work
      | .error diagnostic => throwError diagnostic
    debit typeWork
    let context : MatchContext := {
      theoremName := event.key.theoremName
      selected := name
      descriptor
      body }
    let actualType ← inferType actual
    unless ← matchesPlan context type actualType do throwError "unclassified_form:dtr.signature_mismatch"
    let exposed ← forwardActual event.key.theoremName name actual
    if !(← equalRaw descriptor exposed) && !(← matchesPlan context body exposed) then
      throwError "unclassified_form:dtr.realization_mismatch"
    let .ok (descriptorIdentity, descriptorWork) := TemplateAudit.rawIdentity event.levelParams descriptor (← get).remaining
      | throwError "incomplete_closure:dtr.descriptor_identity"
    debit descriptorWork
    let .ok (actualIdentity, actualWork) := TemplateAudit.rawIdentity event.levelParams actual (← get).remaining
      | throwError "incomplete_closure:dtr.actual_identity"
    debit actualWork
    let argumentInputs ← argumentNames.mapM inputIdentity
    let extractionNames := ((← get).extractionNames.insert event.realizationName).toArray
    let extractionInputs ← extractionNames.mapM inputIdentity
    let certificate : TemplateBindingCertificate := {
      evidenceRef := "", key := event.key, planIdentity := plan.planIdentity,
      descriptorIdentity, actualIdentity, argumentInputs, extractionInputs }
    let .ok (evidenceRef, evidenceWork) := bindingIdentity event.statementIdentity certificate (← get).remaining
      | throwError "incomplete_closure:E8.evidence_identity"
    debit evidenceWork
    return { certificate with evidenceRef }
  let (certificate, _) ← compare.run { remaining := budget - argumentWork, constructorTypes := plan.constructorTypes }
  NativeCoherence.validate (#[plan.definitionOwner, plan.enrollmentOwner,
    event.key.registrationModule, bindingOwner] ++
    (plan.dependencies ++ certificate.argumentInputs ++ certificate.extractionInputs).map (·.owner))
  return certificate

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
  | none => return { occurrence := event, descriptor := none, bindingOwner := none, result := .undeclared }
  | some claim =>
    let result ← tryCatchRuntimeEx
      (withCumulativeBudget do
        unless claim.key == event.key && claim.arena.equal event.arena do
          throwError "unclassified_form:dtr.claim_occurrence"
        if let some diagnostic := claim.resolutionDiagnostic then throwError diagnostic
        let some descriptor := claim.descriptor
          | throwError "unclassified_form:dtr.missing_template"
        let certificate ← validate event descriptor claim.owner
        pure <| TemplateBindingResult.declaredValidated certificate)
      (fun error => do
        let message ← error.toMessageData.toString
        let reason := if message.startsWith "unclassified_form:" || message.startsWith "forbidden_dependency:"
            || message.startsWith "incomplete_closure:" then message else "incomplete_closure:E8.assessment:" ++ message
        let provenance ← diagnosticProvenance event claim reason
        return .declaredUnresolved (diagnosticMessage event.key reason provenance))
    return { occurrence := event, descriptor := claim.descriptor, bindingOwner := some claim.owner, result }

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
  inputs : Array SourceInput

private initialize assessmentCache : EnvExtension (Std.HashMap TemplateOccurrenceKey CachedAssessment) ←
  registerEnvExtension (pure {})

private def sameCacheObject (a b : α) : Bool := unsafe ptrEq a b

private def sameCacheEvent (a b : TemplateOccurrenceEvent) : Bool :=
  a.key == b.key && a.unitName == b.unitName && a.realizationName == b.realizationName &&
  a.statement.equal b.statement && a.levelParams == b.levelParams &&
  a.statementIdentity == b.statementIdentity && a.arena.equal b.arena &&
  a.registrationSource == b.registrationSource &&
  a.registrationSourceIdentity == b.registrationSourceIdentity

private def sameCacheClaim (a b : TemplateBindingClaim) : Bool :=
  a.key == b.key && a.owner == b.owner && a.arena.equal b.arena &&
  a.resolutionDiagnostic == b.resolutionDiagnostic && (match a.descriptor, b.descriptor with
    | none, none => true
    | some a, some b => a.equal b
    | _, _ => false)

private def cacheCurrent (cached : CachedAssessment) (event : TemplateOccurrenceEvent)
    (claim : TemplateBindingClaim) : MetaM Bool := do
  unless sameCacheEvent cached.record.occurrence event do return false
  unless sameCacheClaim cached.claim claim do return false
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
    validateSourceInputs cached.inputs
    NativeCoherence.validate (#[claim.owner, event.key.registrationModule] ++
      cached.constants.map (fun (_, _, owner, _) => owner))
    return true
  catch _ => return false

private def retainAssessment (record : BindingRecord) (claim : TemplateBindingClaim)
    (certificate : TemplateBindingCertificate) : MetaM Unit := do
  let some descriptor := claim.descriptor | return
  let .const name _ := descriptor.getAppFn | return
  let env ← getEnv
  let .ok plan := selectedPlan env name | return
  let mut names : NameSet := {}
  for dependency in plan.dependencies ++ certificate.argumentInputs ++ certificate.extractionInputs do
    names := names.insert dependency.name
  for name in #[plan.name, record.occurrence.key.theoremName, record.occurrence.unitName,
      record.occurrence.realizationName, record.occurrence.key.objectArena] do
    names := names.insert name
  let mut paths := plan.sourceInputs.map (·.path)
  for path in #[record.occurrence.registrationSource, TemplateAudit.sourcePath claim.owner] do
    unless paths.contains path do paths := paths.push path
  let mut constants := #[]
  for name in names do
    let info ← getConstInfo name
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    constants := constants.push (name, info, owner, cacheSemantics env name)
    if owner.toString.startsWith "D5." || owner.toString.startsWith "LeanInformationAudit." then
      let path := TemplateAudit.sourcePath owner
      unless paths.contains path do paths := paths.push path
  let inputs ← (paths.qsort (· < ·)).mapM fun path => readSourceInput path
  let cached : CachedAssessment := {
    record, claim, constants, inputs, options := ← getOptions,
    registry := InformationRegistry.entries env, planName := name, planIdentity := plan.planIdentity }
  modifyEnv fun env => assessmentCache.modifyState env (·.insert record.occurrence.key cached)

/-- Every caller uses the same assessment. A hit requires exact occurrence,
claim, selected plan, options, native dependencies and current source bytes.
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
        ("incomplete_closure:dtr.cache_inputs:" ++ (← error.toMessageData.toString)) Json.null
      return { record with result := .declaredUnresolved diagnostic }
  return record


end LeanInformationAudit.TemplateBinding
