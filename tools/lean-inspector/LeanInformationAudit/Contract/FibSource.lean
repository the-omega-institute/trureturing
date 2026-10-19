import LeanInformationAudit.CompiledSourceScope
import LeanInformationAudit.Contract.Literal
import LeanInformationAudit.Sha256
import LeanInformationAudit.AuricFibCapture

namespace LeanInformationAudit.FibSource
open Lean CompiledSourceScope

abbrev M := CompiledSourceScope.M

def fail (reason : String) : M α := liftM (m := IO) (throw (IO.userError reason) : IO α)

def identity (value : Expr) : String := Sha256.hex (reprStr value).toUTF8

def describe (value : Expr) : Json := Json.mkObj [
  ("identity", toJson (identity value)),
  ("head", toJson (value.getAppFn.constName?.map Name.toString)),
  ("argument_count", toJson value.getAppNumArgs)]

/-- Administrative reduction of compiler-owned constructor data. Recursive definitions,
external implementations and recursors are never executed to obtain metadata. -/
partial def constructorHead (e : Expr) (depth : Nat := 0) : M Expr := do
  debit
  if depth > 256 then fail "fib.selection_data_depth"
  let child := fun e => constructorHead e (depth + 1)
  match e with
  | .mdata _ body => child body
  | .letE _ _ value body _ => child (body.instantiate1 value)
  | .proj name index base =>
    let base ← child base
    let .ctorInfo ctor ← getConstInfo (base.getAppFn.constName?.getD .anonymous)
      | fail "fib.selection_projection"
    unless ctor.induct == name && index < ctor.numFields &&
        base.getAppNumArgs == ctor.numParams + ctor.numFields do
      fail "fib.selection_projection"
    child base.getAppArgs[ctor.numParams + index]!
  | .app .. | .const .. =>
    let head := e.getAppFn
    if head.isLambda then return ← child (head.beta e.getAppArgs)
    let some name := head.constName? | fail "fib.selection_data_constructor"
    if name == ``List.toArray then return e
    for n in [1:9] do
      if name == (.str ``Lean.Name s!"mkStr{n}") then return e
    match ← getConstInfo name with
    | .ctorInfo _ => return e
    | .defnInfo info =>
      unless info.safety == .safe && !(← read).recursive name &&
          !(← read).implementedBy name && !(← read).extern name &&
          head.constLevels!.length == info.levelParams.length do
        fail "fib.selection_unsupported_definition"
      child ((info.value.instantiateLevelParams info.levelParams head.constLevels!).beta e.getAppArgs)
    | _ => return e
  | _ => return e

/-- Only compiler record layouts determine the positions of evidence fields. -/
def fields (constructor : Name) (value : Expr) : M (Array Expr) := do
  let value ← constructorHead value
  let .ctorInfo layout ← getConstInfo constructor | fail "fib.constructor_layout"
  unless value.isAppOfArity constructor (layout.numParams + layout.numFields) do
    fail s!"fib.cannot_decode_constructor:{constructor}:{value.getAppFn.constName?.getD .anonymous}"
  return value.getAppArgs.extract layout.numParams value.getAppNumArgs

/-- Literal selection trees retain array/name syntax without evaluating it. -/
private partial def selectionData (e : Expr) (depth : Nat := 0) : M Expr := do
  debit
  if depth > 256 then fail "fib.selection_data_depth"
  let child := fun e => selectionData e (depth + 1)
  let e ← constructorHead e
  if e.isLit then return e
  let head := e.getAppFn
  let some name := head.constName? | fail "fib.selection_data_constructor"
  let args := e.getAppArgs
  if name == ``List.toArray && args.size == 2 then
    return mkApp2 head args[0]! (← child args[1]!)
  for n in [1:9] do
    if name == (.str ``Lean.Name s!"mkStr{n}") && args.size == n then
      return mkAppN head (← args.mapM child)
  let .ctorInfo ctor ← getConstInfo name | fail "fib.selection_data_constructor"
  unless args.size == ctor.numParams + ctor.numFields do fail "fib.selection_data_arity"
  return mkAppN head (args.extract 0 ctor.numParams ++
    (← (args.extract ctor.numParams args.size).mapM child))

def selection (source : Expr) : M SourceSelection := do
  let term ← selectionData (← projectField `LeanInformationAudit.Analysis.Source.selection source)
  let selected ← IO.ofExcept (Contract.Literal.sourceSelection term)
  return {
    owner := selected.owner
    definition := selected.definition.map fun d => { owner := d.owner, name := d.name, path := d.path }
    coordinates := selected.coordinates
    readouts := selected.readouts.map fun r => {
      path := r.path, stateBinder := r.stateBinder, functionOperand := r.functionOperand,
      stateOperand := r.stateOperand, booleanPredicate := r.booleanPredicate } }

/-- Match the indexed occurrence syntactically. Proof irrelevance and an equal
proposition do not identify two source occurrences. -/
def indexed (head : Name) (value occurrence : Expr) : M Unit := do
  let type ← normalizeHead (← projectType value)
  unless type.isAppOfArity head 2 && type.getAppArgs[1]!.equal occurrence do
    fail "fib.source_occurrence_mismatch"

structure Bound where
  source : Expr
  plan : Expr
  acquisition : Expr
  signature : Expr
  unobserved : Bool
  roles : Array Expr
  task : Nat
  initial : Array Nat
  additions : Array (Array Nat)
  planReason : String
  binding : Json

private def roleIndex (roles : Array Expr) (term : Expr) : M Nat := do
  for i in [:roles.size] do
    if ← sameShape term roles[i]! then return i
  fail "fib.plan_role_not_in_source"

private def roleList (roles : Array Expr) (term : Expr) : M (Array Nat) := do
  let mut term := term
  let mut result := #[]
  repeat
    term ← constructorHead term
    if term.isAppOfArity ``List.nil 1 then return result
    unless term.isAppOfArity ``List.cons 3 do fail "fib.plan_list_unavailable"
    if result.size >= 64 then fail "fib.plan_role_limit"
    result := result.push (← roleIndex roles term.getAppArgs[1]!)
    term := term.getAppArgs[2]!

/-- Retain the original rigid declaration as well as the explicit universe
substitution. Specializing universes never erases the original telescope. -/
def occurrenceBinding (original : ConstantInfo) (occurrence : Expr) : Json := Json.mkObj [
  ("source_name", toJson original.name.toString),
  ("original_type", describe original.type),
  ("original_universes", toJson (original.levelParams.map Name.toString)),
  ("occurrence", describe occurrence),
  ("universe_arguments", toJson (occurrence.getAppFn.constLevels!.map reprStr)),
  ("arguments", toJson (occurrence.getAppArgs.map describe))]

/-- Source reconstruction and every source readout are shared with the ordinary
compiler assessor. This function neither runs nor assigns its four-slot audit. -/
def bind (original info : ConstantInfo) (occurrence client : Expr) : M Bound := do
  indexed `LeanInformationAudit.Analysis.Client client occurrence
  let source ← projectField `LeanInformationAudit.Analysis.Client.source client
  indexed `LeanInformationAudit.Analysis.Source source occurrence
  let selected ← selection source
  -- A selected proposition definition can use fewer or permuted universes.
  -- Read its exact occurrence from the already specialized original statement.
  let definitionOccurrence := if selected.definition.any (·.path == #["arg"]) &&
      info.type.isAppOfArity ``Not 1 then info.type.getAppArgs[0]! else info.type
  let definitionLevels ← match selected.definition with
    | none => pure occurrence.constLevels!
    | some definition => do
      unless definition.path.isEmpty ||
          (definition.path == #["arg"] && info.type.isAppOfArity ``Not 1) do
        fail "unclassified_form:source.definition_path"
      let .const _ levels := definitionOccurrence
        | fail "unclassified_form:source.definition_reference"
      pure levels
  let unobserved := selected.readouts.isEmpty
  let scope ← if unobserved then resolveOriginal info selected definitionLevels
    else resolve info selected definitionLevels
  let actual ← projectField `LeanInformationAudit.Analysis.Source.actual source
  let signature ← projectField `LeanInformationAudit.Analysis.Source.signature source
  let law ← projectField `LeanInformationAudit.Analysis.Source.rebuild source #[actual]
  reconstruct scope.expanded law
  if unobserved then
    unless selected.coordinates.isEmpty &&
        (← sameShape signature (mkConst `LeanInformationAudit.Analysis.unobservedSignature)) &&
        (← sameShape actual (mkConst `LeanInformationAudit.Analysis.unobservedActual)) do
      fail "fib.unobserved_model_mismatch"
  else validateFields scope signature actual
  let roles ← query <| Contract.CompiledExpressions.finiteIndices
    (← projectField `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.finiteRole signature)
  let plan ← projectField `LeanInformationAudit.Analysis.Client.plan client
  let mut task := 0
  let mut initial := #[]
  let mut additions := #[]
  let mut planReason := ""
  try
    task ← roleIndex roles (← projectField `LeanInformationAudit.Analysis.Plan.task plan)
    initial ← roleList roles (← projectField `LeanInformationAudit.Analysis.Plan.initial plan)
    let mut pending ← projectField `LeanInformationAudit.Analysis.Plan.additions plan
    repeat
      pending ← constructorHead pending
      if pending.isAppOfArity ``List.nil 1 then break
      unless pending.isAppOfArity ``List.cons 3 do fail "fib.plan_layers_unavailable"
      if additions.size >= 64 then fail "fib.plan_layer_limit"
      additions := additions.push (← roleList roles pending.getAppArgs[1]!)
      pending := pending.getAppArgs[2]!
  catch error => planReason := error.toString
  let binding := Json.mkObj [
    ("occurrence", occurrenceBinding original occurrence),
    ("source_owner", toJson selected.owner.toString),
    ("definition", selected.definition.map (fun d => Json.mkObj [
      ("owner", toJson d.owner.toString), ("name", toJson d.name.toString),
      ("path", toJson d.path)]) |>.getD Json.null),
    ("expanded_source", describe scope.expanded),
    ("telescope_size", toJson scope.telescope.size),
    ("level_count", toJson original.levelParams.length),
    ("source", describe source), ("signature", describe signature),
    ("actual", describe actual), ("rebuild", describe law),
    ("coordinates", toJson selected.coordinates),
    ("readouts", toJson (scope.readouts.mapIdx fun i r => Json.mkObj [
      ("role", toJson i), ("path", toJson selected.readouts[i]!.path),
      ("scope_size", toJson r.rawContext.size),
      ("observation", describe (r.rawContext.foldr (fun b e =>
        if let some v := b.value then Expr.letE b.name b.domain v e b.nondep
        else Expr.lam b.name b.domain e b.info) r.rawObservation))])),
    ("source_correspondence", toJson (if unobserved then
      "compiled full reconstruction; terminal model with no source data observations"
      else "compiled full reconstruction and actual readout correspondence")),
    ("ordinary_registration", toJson "independent; no audit status assigned")]
  return {
    source := source, plan := plan, signature := signature, unobserved := unobserved, roles := roles,
    task := task, initial := initial, additions := additions, planReason := planReason, binding := binding,
    acquisition := ← projectField `LeanInformationAudit.Analysis.Client.acquisition client }

def planJson (bound : Bound) : Json := Json.mkObj [
  ("available", toJson bound.planReason.isEmpty), ("reason", toJson bound.planReason),
  ("source_plan", describe bound.plan),
  ("roles", toJson (bound.roles.map describe)),
  ("task", if bound.planReason.isEmpty then toJson bound.task else Json.null),
  ("initial", if bound.planReason.isEmpty then toJson bound.initial else Json.null),
  ("additions", if bound.planReason.isEmpty then toJson bound.additions else Json.null),
  ("scope", toJson "same actual realization; initial layer and every ordered addition"),
  ("kernel", toJson "equality of selected actual source readouts"),
  ("refinement", toJson "weak; empty, repeated and zero-gain layers retained")]

end LeanInformationAudit.FibSource

namespace LeanInformationAudit.FibLaw
open Lean CompiledSourceScope FibSource

private def base : Name := `LeanInformationAudit.AuricFib.Contract

private def field (family : Expr) (name : String) : FibSource.M Expr :=
  projectField ((base ++ `LawFamily).str name) family

private def list (value : Expr) : FibSource.M (Array Expr) := do
  let mut pending := value
  let mut values := #[]
  repeat
    let term ← constructorHead pending
    if term.isAppOfArity ``List.nil 1 then return values
    unless term.isAppOfArity ``List.cons 3 do fail "fib.law_requires_literal_list"
    if values.size ≥ 64 then fail "fib.law_list_limit"
    values := values.push term.getAppArgs[1]!
    pending := term.getAppArgs[2]!

private def option (value : Expr) : FibSource.M (Option Expr) := do
  let term ← constructorHead value
  if term.isAppOfArity ``Option.none 1 then return none
  unless term.isAppOfArity ``Option.some 2 do fail "fib.law_requires_literal_option"
  return some term.getAppArgs[1]!

private def atom (value : Expr) : FibSource.M Nat := do
  let term ← constructorHead value
  for (i, name) in #["zero", "low", "high", "ends", "middle"].toList.zipIdx do
    if term.isConstOf ((`D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window).str i) then
      return name
  fail "fib.law_atom_unavailable"

private def rationalCells (value : Expr) (task : Bool := false) : FibSource.M Json := do
  let name := if task then base ++ `LawTask.mk else base ++ `Masses.mk
  let cells ← fields name value
  let find := (← read).provenance.view.find?
  let denominator ← IO.ofExcept (Contract.Literal.referencedValue find cells[5]!)
  let denominator ← IO.ofExcept (Contract.Literal.nat "fib.law_denominator" denominator)
  let values ← (cells.extract 0 5).mapM fun cell => do
    let cell ← IO.ofExcept (Contract.Literal.referencedValue find cell)
    let n ← if task then IO.ofExcept (Contract.Literal.int "fib.law_task" cell)
      else do pure (Int.ofNat (← IO.ofExcept (Contract.Literal.nat "fib.law_mass" cell)))
    return toJson s!"{n}/{denominator}"
  return Json.arr values

/-- Read proof terms without their type annotations. Source record projections
are reduced before traversal so phantom occurrence indices are not result use. -/
private def bodyNames (value : Expr) : FibSource.M (Array Name) := do
  let mut pending := [value]
  let mut seen : Std.HashSet Expr := {}
  let mut names : NameSet := {}
  while let value :: rest := pending do
    pending := rest
    debit
    if seen.contains value then continue
    seen := seen.insert value
    match value with
    | .const name _ => names := names.insert name
    | .mdata _ body | .lam _ _ body _ => pending := body :: pending
    | .letE _ _ term body _ => pending := body.instantiate1 term :: pending
    | .proj _ _ term =>
      let reduced ← try constructorHead value catch _ => pure value
      pending := (if reduced.equal value then term else reduced) :: pending
    | .app .. =>
      let fn := value.getAppFn
      if fn.isLambda then
        pending := fn.beta value.getAppArgs :: pending
        continue
      if let some name := fn.constName? then
        if let some projection := (← read).provenance.view.getProjectionFnInfo? name then
          let args := value.getAppArgs
          if args.size > projection.numParams then
            let projected ← projectField name args[projection.numParams]!
            let selected ← try constructorHead projected catch _ => pure projected
            pending := mkAppN selected (args.extract (projection.numParams + 1) args.size) :: pending
          -- A partial projection has only structure parameters, including indices.
          continue
      let arguments := value.getAppArgs
      let start ← if let some name := fn.constName? then do
          let info ← getConstInfo name
          -- A type-valued application is an annotation, including its indices.
          -- Its occurrence arguments do not use a theorem's proof result.
          if info.type.getForallBody.isSort then pure arguments.size else
          match info with
          | .ctorInfo layout => pure layout.numParams
          | _ => pure 0
        else pure 0
      pending := fn :: (arguments.extract start arguments.size).toList ++ pending
    | _ => pure ()
  return names.toArray

/-- This is syntactic proof-body dependency metadata, including private lemmas;
it neither measures novelty nor replaces the proof-escape live-path judgment. -/
private def usesTarget (target : Name) (proof : Expr) : FibSource.M Bool := do
  let targetOwner ← ownerOf target
  let some targetIndex := (← read).moduleIndex? targetOwner
    | fail "fib.law_target_module_unavailable"
  let mut pending := (← bodyNames proof).toList
  let mut seen : NameSet := {}
  while let name :: rest := pending do
    pending := rest
    debit
    if name == target then return true
    if seen.contains name then continue
    seen := seen.insert name
    let owner ← ownerOf name
    let some index := (← read).moduleIndex? owner
      | fail "fib.law_dependency_module_unavailable"
    -- Import order is topological: an earlier module cannot use the target.
    -- Prune that entire library closure before reading its proof bodies.
    if index < targetIndex then continue
    let info ← getConstInfo name
    let proofDeclaration ← match info with
      | .thmInfo _ => pure true
      | .defnInfo _ | .opaqueInfo _ => isProp info.type
      | _ => pure false
    if proofDeclaration then
      if let some body := info.value? (allowOpaque := true) then
        pending := (← bodyNames body).toList ++ pending
  return false

private def facts (target : Name) (value : Expr) : FibSource.M (Json × AuricFib.Capture) := do
  let mut separated := false
  let mut identifiable := false
  let mut results := #[]
  for term in ← list value do
    let term ← constructorHead term
    let head := term.getAppFn.constName?.getD .anonymous
    let mut kind := ""
    for name in ["deltaSign", "positiveWidth", "identifiable", "separated"] do
      if head == (base ++ `LawFact).str name then kind := name
    if kind.isEmpty then fail "fib.law_fact_outside_allowlist"
    if kind == "separated" then separated := true
    if kind == "identifiable" then identifiable := true
    let values ← fields head term
    let proof := values.back!
    let sign ← if kind == "deltaSign" then do
        let sign ← constructorHead values[0]!
        pure (toJson sign.getAppFn.constName!.getString!)
      else pure Json.null
    results := results.push <| Json.mkObj [("kind", toJson kind), ("sign", sign),
      ("proof", describe proof), ("uses_target_results", toJson (← usesTarget target proof))]
  if separated && identifiable then fail "fib.law_inconsistent_capture_evidence"
  return (Json.arr results, AuricFib.classifyCapture separated identifiable)

/-- Only a fixed mode type and mass-valued selected observation are supported.
Source occurrence, complete telescope and actual readout binding are acquired
by the existing Analysis.Client path before any law data is decoded. -/
def request (bound : Bound) (target : Name) (family point claims task : Expr) : FibSource.M Json := do
  discard <| fields (base ++ `LawFamily.mk) family
  if bound.unobserved then fail "fib.law_requires_selected_mass_readout"
  let mode ← field family "Mode"
  let params ← projectField
    `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Params bound.signature
  withLocal `parameter .default params none fun θ => do
    let state ← projectField
      `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State bound.signature #[θ]
    unless ← sameShape state mode do fail "fib.law_state_depends_on_parameter"
  let role ← field family "role"
  unless ← bound.roles.anyM (sameShape role) do fail "fib.law_role_not_selected"
  let graph ← (← list (← field family "atoms")).mapM fun pair => do
    let values ← fields ``Prod.mk pair
    return (← atom values[1]!, describe values[0]!)
  unless graph.size == 5 && (graph.map Prod.fst).toList.eraseDups.length == 5 do
    fail "fib.law_atom_pairing_not_bijective"
  let mut pointJson := Json.null
  let mut pointError := ""
  try
    if let some point ← option point then
      discard <| fields (base ++ `LawPoint.mk) point
      let parameter ← projectField (base ++ `LawPoint.parameter) point
      let masses ← projectField (base ++ `LawPoint.masses) point
      pointJson := Json.mkObj [("parameter", describe parameter),
        ("law", ← rationalCells masses), ("certificate", describe point)]
  catch error => pointError := error.toString
  let taskValue ← option task
  let taskJson ← match taskValue with
    | none => pure Json.null
    | some task => rationalCells task true
  let (factsJson, capture) ← facts target claims
  let usesDelta ← match taskValue with
    | none => pure false
    | some task => do
      let cells ← fields (base ++ `LawTask.mk) task
      let find := (← read).provenance.view.find?
      let values ← (cells.extract 0 4).mapM fun cell => do
        IO.ofExcept (Contract.Literal.int "fib.law_task"
          (← IO.ofExcept (Contract.Literal.referencedValue find cell)))
      pure (values[3]! - values[1]! - values[2]! + values[0]! != 0)
  let infinite := (← option (← field family "infinite")).isSome
  let simplex := (← option (← field family "simplex")).map describe
  return Json.mkObj [
    ("arena", toJson "law-family"), ("binding", bound.binding),
    ("plan", planJson bound),
    ("acquisition", Json.mkObj [("kind", toJson (if infinite then "infinite" else "unavailable")),
      ("reason", toJson (if infinite then "proved infinite parameter domain; no finite pair denominator"
        else "no complete finite parameter-domain presentation"))]),
    ("law_family", Json.mkObj [
      ("domain", describe (← field family "domain")), ("law", describe (← field family "law")),
      ("simplex_coverage", toJson simplex),
      ("law_eq", describe (← field family "law_eq")),
      ("nonnegative", describe (← field family "nonnegative")),
      ("normalized", describe (← field family "normalized")),
      ("mode_pairing", toJson (graph.map fun (atom, mode) =>
        Json.mkObj [("atom", toJson atom), ("mode", mode)]))]),
    ("point", pointJson), ("point_unavailable_reason", toJson pointError),
    ("facts", factsJson), ("task", taskJson),
    ("compiled_capture", Json.mkObj [
      ("family", Json.mkObj [("status", toJson capture.label),
        ("simplex_width_implies_strict", toJson false),
        ("inheritance", toJson (if capture == .strict && simplex.isSome then
          "simplex-inherited" else "unassessed")),
        ("reason", toJson (if capture == .unknown then
          "no family separation or identifiability witness supplied" else "compiled family witness"))]),
      ("reading", Json.mkObj [("kind", toJson (if capture == .unknown then "unknown" else "available")),
        ("reason", toJson (if capture == .unknown then
          "no family separation or identifiability witness supplied" else "compiled family witness"))]),
      ("task", toJson (AuricFib.taskCapture capture usesDelta).label),
      ("uses_delta", toJson usesDelta)])]

end LeanInformationAudit.FibLaw
