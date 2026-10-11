import LeanInformationAudit.CompiledSourceScope
import LeanInformationAudit.Contract.Literal
import LeanInformationAudit.Sha256

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
  let scope ← resolve info selected definitionLevels
  let actual ← projectField `LeanInformationAudit.Analysis.Source.actual source
  let signature ← projectField `LeanInformationAudit.Analysis.Source.signature source
  let law ← projectField `LeanInformationAudit.Analysis.Source.rebuild source #[actual]
  reconstruct scope.expanded law
  validateFields scope signature actual
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
    ("source_correspondence", toJson "compiled full reconstruction and actual readout correspondence"),
    ("ordinary_registration", toJson "independent; no audit status assigned")]
  return {
    source := source, plan := plan, signature := signature, roles := roles,
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
