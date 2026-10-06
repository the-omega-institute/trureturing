import LeanInformationAudit.CompiledSourceContract
import LeanInformationAudit.CompiledEvidence

namespace LeanInformationAudit.CompiledAssessment
open Lean TemplateAudit CompiledEvidence


structure Context where
  enrollment : CompiledEnrollment.Context
  plans : TemplateIndex

abbrev M := ReaderT Context IO

private def fail [Monad m] [MonadLiftT IO m] (reason : String) : m α :=
  liftM (m := IO) (throw (IO.userError reason) : IO α)

private def view : M RegistrationGates.CompiledView := return (← read).enrollment.provenance.view
private def getConstInfo (name : Name) : M ConstantInfo := do
  let some info := (← view).find? name | fail s!"incomplete_closure:dtr.compiled_constant:{name}"
  return info
private def getOptions : M Options := return (← read).enrollment.provenance.options
private def evidence (action : CompiledEvidence.Q α) : M α := do
  action.run (← read).enrollment.provenance
private def eraseProofs (e : Expr) (fuel : Nat := 524288) : M (Expr × Nat) :=
  evidence (CompiledEvidence.eraseProofs e fuel)
private def rawIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) :=
  evidence (CompiledEvidence.rawIdentity params e fuel)
private def isRecursiveDefinition (name : Name) : M Bool := return (← read).enrollment.recursive name
private def isProp (e : Expr) : M Bool :=
  evidence (RegistrationGates.compiledQuery (Contract.CompiledExpressions.propositionShape e))
private def projectType (e : Expr) : M Expr :=
  evidence (RegistrationGates.compiledQuery (Contract.CompiledExpressions.typeShape e))
private def isProof (e : Expr) : M Bool := do isProp (← projectType e)
private def checkExtractionType (theoremName : Name) (type : Expr) (available : Nat)
    (constructors : Array Name) : M (Array DependencyIdentity × Nat) := do
  (CompiledEnrollment.checkExtractionType theoremName type available constructors).run
    (← read).enrollment
private def templateArguments (theoremName : Name) (arguments : Array Expr) (available : Nat)
    (constructors : Array Name) (indices : Array Bool) : M (Except String (Array Name × Nat)) := do
  try
    return .ok (← (CompiledEnrollment.checkArguments theoremName arguments available
      constructors indices).run (← read).enrollment)
  catch error => return .error error.toString
private def templateTypes (theoremName : Name) (types : Array (Expr × Array Expr))
    (available : Nat) : M (Except String Nat) :=
  evidence (RegistrationGates.Compiled.templateTypesCurrent theoremName types available)
private def selectedPlan (name : Name) : M (Except String TemplatePlanData) :=
  return (← read).plans.lookup name (pure () : Id Unit)
private def checkHeartbeat : M Unit := do
  let context := (← read).enrollment.provenance
  if context.heartbeatLimit != 0 &&
      (← IO.getNumHeartbeats) - context.heartbeatStart > context.heartbeatLimit then
    fail "incomplete_closure:E8.heartbeats"
private def diagnosticFields (message : String) : String :=
  match message.splitOn ":" with
  | reason :: rule :: site =>
    "reason=" ++ reason ++ " rule=" ++ rule ++ " site=" ++
      (Json.str (String.intercalate ":" site)).compress
  | _ => "reason=incomplete_closure rule=E8.exception site=" ++ (Json.str message).compress

private structure CompareState where
  remaining : Nat
  extractionNames : NameSet := {}
  constructorTypes : Array Name := #[]
  nextLocal : Nat := 0

private abbrev CompareM := StateT CompareState M
private def debit (n : Nat := 1) : CompareM Unit := do
  checkHeartbeat
  unless n ≤ (← get).remaining do fail "incomplete_closure:E8.comparison_work"
  modify fun state => { state with remaining := state.remaining - n }


private def withLocal (name : Name) (bi : BinderInfo) (type : Expr)
    (value : Option Expr) (body : Expr → CompareM α) : CompareM α := do
  let context ← read
  let locals := context.enrollment.provenance.locals
  let index := (← get).nextLocal
  modify fun state => { state with nextLocal := index + 1 }
  let id : FVarId := ⟨Name.num `compiledAssessmentLocal index⟩
  let locals := match value with
    | none => locals.mkLocalDecl id name type bi
    | some value => locals.mkLetDecl id name type value
  withReader (fun context : Context => { context with enrollment :=
    { context.enrollment with provenance := { context.enrollment.provenance with locals } } })
      (body (mkFVar id))

private partial def lambdaTelescope (e : Expr) (xs : Array Expr := #[])
    (body : Array Expr → Expr → CompareM α) : CompareM α := do
  match e with
  | .lam name type tail bi =>
    withLocal name bi type none fun x => lambdaTelescope (tail.instantiate1 x) (xs.push x) body
  | _ => body xs e

private def construct (action : Nat → Except String (α × Nat)) : CompareM α := do
  let (result, work) ← match action (← get).remaining with
    | .ok value => pure value
    | .error reason => fail reason
  debit work
  return result

private def eraseInput (e : Expr) : CompareM Expr := do
  let (erased, work) ← eraseProofs e (← get).remaining
  debit work
  return erased

private def materialize (plan : PlanNode) : CompareM Expr :=
  construct (fun fuel => PlanTransform.toExpr plan fuel)

private partial def alpha (e : Expr) (depth : Nat := 0) : CompareM Expr := do
  debit
  if depth > 256 then fail "incomplete_closure:E8.comparison_depth"
  let child := fun x => alpha x (depth + 1)
  match e with
  | .app f a => return .app (← child f) (← child a)
  | .lam _ t b bi => return .lam .anonymous (← child t) (← child b) bi
  | .forallE _ t b bi => return .forallE .anonymous (← child t) (← child b) bi
  | .letE _ t v b nd => return .letE .anonymous (← child t) (← child v) (← child b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ => fail "incomplete_closure:dtr.open_comparison"
  | _ => return e

private def equalRaw (a b : Expr) : CompareM Bool := do
  let (a, aWork) ← eraseProofs a (← get).remaining
  debit aWork
  let (b, bWork) ← eraseProofs b (← get).remaining
  debit bWork
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
  | _ => fail "unclassified_form:dtr.unsaturated_plan"

private def isRealizationType (type : Expr) : Bool :=
  #[`D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
    `LeanInformationAudit.StructuralPrimitiveRealization].contains (type.getAppFn.constName?.getD .anonymous)

/-- Expose only a saturated forwarding spine. Every data parameter must occur
exactly once, in its original order, as a whole argument. Proof parameters and
arguments are opaque; their propositions still pass the shared compiler.
No beta reduction is performed inside an actual supplied argument. -/
private def forwardActual (theoremName selected : Name) (initial : Expr) : CompareM Expr := do
  let mut actual := initial
  let mut visited : NameSet := {}
  for _ in [:256] do
    debit
    let .const name universeArgs := actual.getAppFn | return actual
    if name == selected then return actual
    let some (.defnInfo info) := (← view).find? name | return actual
    unless isRealizationType info.type.getForallBody do return actual
    if visited.contains name || info.safety != .safe ||
        (← isRecursiveDefinition name) || info.all.length > 1 ||
        ((← view).getProjectionFnInfo? name).isSome ||
        (← read).enrollment.implementedBy name ||
        (← read).enrollment.extern name then
      fail "unclassified_form:dtr.extraction_kind"
    let arguments := actual.getAppArgs
    if actual.hasFVar || actual.hasLooseBVars || actual.hasMVar ||
        universeArgs.length != info.levelParams.length then
      fail "incomplete_closure:dtr.extraction_open"
    let erasedValue ← eraseInput info.value
    let forwarding : CompareM Bool :=
      lambdaTelescope erasedValue #[] fun parameters body => do
        unless body.getAppFn.isConst && parameters.size == arguments.size do return false
        let mut expected : Array Expr := #[]
        for parameter in parameters do
          debit
          unless ← isProof parameter do expected := expected.push parameter
        let mut forwarded : Array Expr := #[]
        for argument in body.getAppArgs do
          debit
          unless ← isProof argument do
            if argument.hasFVar then
              unless argument.isFVar do return false
              forwarded := forwarded.push argument
        return forwarded == expected
    unless ← forwarding do return actual
    let (dependencies, typeWork) ← checkExtractionType theoremName info.type
      (← get).remaining (← get).constructorTypes
    debit typeWork
    let indices := CompiledEnrollment.typePositions info.type
    debit indices.size
    let (argumentNames, argumentWork) ← match ←
        templateArguments theoremName arguments (← get).remaining
          (← get).constructorTypes indices with
      | .ok result => pure result
      | .error diagnostic => fail diagnostic
    debit argumentWork
    let names := dependencies.map (·.name) ++ argumentNames
    modify fun state =>
      let extracted := names.foldl (fun found n => found.insert n)
        (state.extractionNames.insert name)
      { state with extractionNames := extracted }
    let .ok (_, bodyWork) ← rawIdentity info.levelParams info.value (← get).remaining
      | fail "incomplete_closure:E8.extraction_body"
    debit bodyWork
    let mut value ← construct (fun fuel => PlanTransform.instantiateExpr erasedValue info.levelParams universeArgs fuel)
    for argument in arguments do
      let .lam _ _ tail _ := value | fail "incomplete_closure:dtr.extraction_telescope"
      value ← rawSubstitute tail argument 0
    visited := visited.insert name
    actual := value
  fail "incomplete_closure:E8.extraction_depth"

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
  if depth > 256 then fail "incomplete_closure:E8.extraction_depth"
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
  if depth > 256 then fail "incomplete_closure:E8.type_obligation_depth"
  let child := fun p => retainedTypes p context (depth + 1)
  let obligation := fun type : Expr => (type, if type.hasLooseBVars then context else #[])
  match plan with
  | .atom _ | .supplied _ => return #[]
  | .proofLeaf type => return #[obligation type]
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
  if depth > 256 then fail "incomplete_closure:E8.type_obligation_depth"
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

private def fixedProjection (actual : Expr) : M (Option FixedProjection) := do
  match actual with
  | .proj typeName index base => return some { typeName, index, base }
  | _ =>
    let .const name universeArgs := actual.getAppFn | return none
    let some projection := (← view).getProjectionFnInfo? name | return none
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
  if depth > 256 then fail "incomplete_closure:E8.match_depth"
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
          if let some (.ctorInfo info) := (← view).find? ctor then
            if info.induct == projection.typeName && info.numParams + projection.index < fields.size &&
                (projection.parameters.isEmpty || projection.parameters.size == info.numParams) &&
                (projection.universeArgs.isNone || projection.universeArgs == some universeArgs) then
              let mut parametersMatch := true
              for i in [:projection.parameters.size] do
                unless ← child fields[i]! projection.parameters[i]! do parametersMatch := false
              if parametersMatch then
                return ← child plan (← materialize fields[info.numParams + projection.index]!)
      else if let .const ctor universeArgs := base.getAppFn then
        if let some (.ctorInfo info) := (← view).find? ctor then
          let fields := base.getAppArgs
          if info.induct == projection.typeName && fields.size == info.numParams + info.numFields &&
              projection.index < info.numFields &&
              (projection.parameters.isEmpty || projection.parameters.size == info.numParams) &&
              (projection.universeArgs.isNone || projection.universeArgs == some universeArgs) then
            -- Audit the entire literal receiver before selecting a field. An
            -- unused anchor or signature parameter is still an extraction input.
            let indices := CompiledEnrollment.typePositions info.type
            debit (indices.size + projection.parameters.size)
            let (names, work) ← match ← templateArguments
                context.theoremName (fields ++ projection.parameters) (← get).remaining
                (← get).constructorTypes (indices ++ indices.extract 0 projection.parameters.size) with
              | .ok result => pure result
              | .error diagnostic => fail diagnostic
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
  | .atom raw | .supplied raw => equalRaw raw actual
  | .proofLeaf type =>
    unless ← isProof actual do return false
    equalRaw type (← projectType actual)
  | .app (.lam _ body _) arg => child (← substitute body arg) actual
  | .app f a =>
    match actual with
    | .app g b => return (← child f g) && (← child a b)
    | _ => return false
  | .lam t b bi =>
    match actual with
    | .lam _ u c bj =>
      unless bi == bj && (← child t u) do return false
      withLocal .anonymous bj u none fun x => do
        child (← substitute b (.atom x)) (c.instantiate1 x)
    | _ => return false
  | .forallE t b bi =>
    match actual with
    | .forallE _ u c bj =>
      unless bi == bj && (← child t u) do return false
      withLocal .anonymous bj u none fun x => do
        child (← substitute b (.atom x)) (c.instantiate1 x)
    | _ => return false
  | .letE t v b nd =>
    match actual with
    | .letE _ u w c ne =>
      unless nd == ne && (← child t u) && (← child v w) do return false
      withLocal .anonymous .default u (some w) fun x => do
        child (← substitute b (.atom x)) (c.instantiate1 x)
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
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 ||
      info.type.isAppOfArity escapeForwardBridge 3 ||
      info.type.isAppOfArity escapeWitnessBridge 3 then
    pure info.type.getAppArgs[2]!
  else if isRealizationType info.type then
    match info with
    | .defnInfo defn =>
      if defn.safety != .safe || (← isRecursiveDefinition name) || defn.all.length > 1 ||
          (← read).enrollment.implementedBy name ||
          (← read).enrollment.extern name then
        fail "unclassified_form:dtr.extraction_kind"
      pure defn.value
    | _ => fail "unclassified_form:dtr.extraction_kind"
  else fail "unclassified_form:dtr.extraction_interface"
  -- The named realization is used at the occurrence's rigid universe telescope.
  -- Renaming its binders is permitted; permutation or arity guessing is not.
  let raw ← eraseInput raw
  if info.levelParams.isEmpty then return raw
  unless info.levelParams.length == event.levelParams.length do
    fail "unclassified_form:dtr.extraction_universes"
  construct fun fuel => PlanTransform.instantiateExpr raw info.levelParams
    (event.levelParams.map Level.param) fuel

private def closed (e : Expr) : M Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    fail "incomplete_closure:dtr.descriptor_open"

private def inputIdentity (name : Name) : CompareM DependencyIdentity := do
  debit
  let info ← getConstInfo name
  let some owner := (← view).ownerOf name
    | fail s!"incomplete_closure:dtr.input_owner:{name}"
  let .ok (typeIdentity, typeWork) ← rawIdentity info.levelParams info.type (← get).remaining
    | fail "incomplete_closure:dtr.input_identity"
  debit typeWork
  -- Proof implementations contribute no body identity; nested proof arguments
  -- in data inputs are erased by rawIdentity as well.
  let bodyIdentity ← if ← isProp info.type then pure "" else match info.value? with
    | none => pure ""
    | some value =>
      let .ok (identity, bodyWork) ← rawIdentity info.levelParams value (← get).remaining
        | fail "incomplete_closure:dtr.input_identity"
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

def diagnosticMessage (key : TemplateOccurrenceKey) (reason : String)
    (provenance : Json) : String :=
  s!"IE-C050 ClosedTruthReadout key={key.root}/{key.catalog}/{key.theoremName} " ++
    diagnosticFields reason ++ " readout=" ++ (toJson (failureSite reason)).compress ++
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
    (claim : TemplateBindingClaim) (reason : String) : M Json := do
  if reason.startsWith "incomplete_closure:" then return Json.null
  try
    let descriptor := claim.descriptor
    let name := descriptor.bind fun e => e.getAppFn.constName?
    let plan ← match name with
      | some name => pure (← selectedPlan name).toOption
      | none => pure none
    let action : CompareM Json := do
      let mut names : NameSet := {}
      for argument in descriptor.map Expr.getAppArgs |>.getD #[] do
        for name in (← eraseProofs argument).1.getUsedConstants do
          unless name == ``lcProof do names := names.insert name
      let arguments ← (names.toArray.qsort Name.quickLt).mapM inputIdentity
      let extraction ← inputIdentity event.realizationName
      return Json.mkObj [
        ("argument_inputs", Json.arr (arguments.map dependencyJson)),
        ("extraction_inputs", Json.arr #[dependencyJson extraction]),
        ("plan_identity", plan.map (toJson ∘ TemplatePlanData.planIdentity) |>.getD Json.null),
        ("rule", toJson (failureRule reason)), ("site", toJson (failureSite reason)),
        ("template_key", name.map (toJson ∘ Name.toString) |>.getD Json.null)]
    let (provenance, _) ← action.run {
      remaining := min 524288 (TemplateAudit.informationTemplate.work.get (← getOptions)) }
    return provenance
  catch _ => return Json.null

def validate (event : TemplateOccurrenceEvent) (descriptor : Expr)
    (_bindingOwner : Name) (escape : EscapeRecordEvidence) (input : EscapeRecordInput) : M TemplateBindingCertificate := do
  closed descriptor
  let .const name universeArgs := descriptor.getAppFn
    | fail "unclassified_form:dtr.descriptor_head"
  let plan ← match ← selectedPlan name with
    | .ok plan => pure plan
    | .error reason => fail reason
  let some owner := (← view).ownerOf name | fail "incomplete_closure:dtr.template_owner"
  unless owner == plan.definitionOwner && universeArgs.length == plan.levelParams.length &&
      descriptor.getAppArgs.size == plan.slots.size do
    fail "unclassified_form:dtr.descriptor_telescope"
  if plan.sourceBound then
    return ← (CompiledSourceContract.validate event descriptor plan input).run (← read).enrollment
  if input.sourceSelection.isSome then fail "unclassified_form:source.plan_kind"
  let initialBudget := min 524288 (TemplateAudit.informationTemplate.work.get (← getOptions))
  let (descriptor, eraseWork) ← eraseProofs descriptor initialBudget
  let arguments := descriptor.getAppArgs
  let budget := initialBudget - eraseWork
  let (argumentNames, argumentWork) ← match ← templateArguments event.key.theoremName arguments budget plan.constructorTypes
      (plan.slots.map fun slot => slot.type.isConstOf ``Nat || slot.kind == .dictionary) with
    | .ok result => pure result
    | .error reason => fail reason
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
      | _ => fail "unclassified_form:dtr.descriptor_telescope"
    obligations := obligations.push ((← materialize type), #[])
    obligations := obligations ++ (← retainedTypes type) ++ (← retainedTypes body)
    let typeWork ← match ← templateTypes event.key.theoremName
        obligations (← get).remaining with
      | .ok work => pure work
      | .error diagnostic => fail diagnostic
    debit typeWork
    let context : MatchContext := {
      theoremName := event.key.theoremName
      selected := name
      descriptor
      body }
    let actualType ← projectType actual
    unless ← matchesPlan context type actualType do fail "unclassified_form:dtr.signature_mismatch"
    let exposed ← forwardActual event.key.theoremName name actual
    if !(← equalRaw descriptor exposed) && !(← matchesPlan context body exposed) then
      fail "unclassified_form:dtr.realization_mismatch"
    if escape.bridgeKind == "witness" && event.compiledMathematics.isNone then
      let rawActual := (← getConstInfo event.realizationName).type.getAppArgs[2]!
      let witness := `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessArena
      let .const _ arenaLevels := (← projectType event.arena).getAppFn
        | fail "incomplete_closure:dtr.witness_arena_type"
      let computed := mkApp (mkConst (witness.str "realization") arenaLevels) event.arena
      let readout (value : Expr) : Expr :=
        .proj `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization 0 value
      let tied ← evidence (RegistrationGates.compiledQuery do
        if ← Contract.CompiledExpressions.sameShape rawActual computed then return true
        Contract.CompiledExpressions.sameShape (readout rawActual) (readout computed))
      unless tied do
        fail "unclassified_form:dtr.witness_readout_tie"
    let .ok (descriptorIdentity, descriptorWork) ← rawIdentity event.levelParams descriptor (← get).remaining
      | fail "incomplete_closure:dtr.descriptor_identity"
    debit descriptorWork
    let .ok (actualIdentity, actualWork) ← rawIdentity event.levelParams actual (← get).remaining
      | fail "incomplete_closure:dtr.actual_identity"
    debit actualWork
    let argumentInputs ← argumentNames.mapM inputIdentity
    let mut retained := (← get).extractionNames.insert event.realizationName
    -- Fingerprint the inspected roots here. Their transitive data/type closure
    -- is retained below without serializing pinned upstream implementations.
    for name in ← evidence (CompiledEvidence.inspectionRoots event) do retained := retained.insert name
    let extractionNames := retained.toArray
    let extractionInputs ← extractionNames.mapM inputIdentity
    let certificate : TemplateBindingCertificate := {
      evidenceRef := "", key := event.key, planIdentity := plan.planIdentity,
      descriptorIdentity, actualIdentity, argumentInputs, extractionInputs, escape }
    let .ok (evidenceRef, evidenceWork) := bindingIdentity event.statementIdentity certificate (← get).remaining
      | fail "incomplete_closure:E8.evidence_identity"
    debit evidenceWork
    return { certificate with evidenceRef }
  let (certificate, _) ← compare.run { remaining := budget - argumentWork, constructorTypes := plan.constructorTypes }
  checkHeartbeat
  return certificate

/-- Registration and final joined assessment share this function. Failure of a
new binding check is retained metadata, never a module elaboration failure. -/
def assess (event : TemplateOccurrenceEvent) (claim : Option TemplateBindingClaim) : M BindingRecord := do
  match claim with
  | none => return {
      occurrence := event, descriptor := none, bindingOwner := none, result := .undeclared
      escape := { bridgeKind := (← evidence (CompiledEvidence.bridgeKind event)) } }
  | some claim =>
    let escape ← evidence (CompiledEvidence.checkEscapeRecord event claim.escapeInput)
    let result ← try
      unless claim.key == event.key && claim.arena.equal event.arena do
        fail "unclassified_form:dtr.claim_occurrence"
      if let some diagnostic := claim.resolutionDiagnostic then fail diagnostic
      let some descriptor := claim.descriptor | fail "unclassified_form:dtr.missing_template"
      let certificate ← validate event descriptor claim.owner escape claim.escapeInput
      checkHeartbeat
      pure <| TemplateBindingResult.declaredValidated certificate
    catch error =>
      let message := error.toString
      let reason := if message.startsWith "unclassified_form:" ||
          message.startsWith "forbidden_dependency:" || message.startsWith "incomplete_closure:" then
        message else "incomplete_closure:E8.assessment:" ++ message
      let provenance ← diagnosticProvenance event claim reason
      pure <| .declaredUnresolved (diagnosticMessage event.key reason provenance)
    return { occurrence := event, descriptor := claim.descriptor, bindingOwner := some claim.owner, result, escape := match result with
      | .declaredValidated certificate => certificate.escape
      | _ => escape }


end LeanInformationAudit.CompiledAssessment
