import LeanInformationAudit.Registry.Enrollment
import LeanInformationAudit.DependentFamilyRealization

namespace LeanInformationAudit.FamilySource
open Lean Meta TemplateAudit

private abbrev M := StateT Nat MetaM
private def debit (n : Nat := 1) : M Unit := do
  Core.checkMaxHeartbeats "family source scope"
  unless n ≤ (← get) do throwError "incomplete_closure:E8.family_source_work"
  modify (· - n)

private def transform (slots : Array Nat) (depth : Nat) (e : Expr)
    (inverse : Bool := false) : M Expr := do
  let .ok (result, work) := PlanTransform.projectCoordinates slots depth e inverse (← get)
    | throwError "unclassified_form:family.source.coordinate_projection"
  debit work
  return result

private def substitute (body value : Expr) : M Expr := do
  let .ok (result, work) := PlanTransform.substituteExpr body value 0 (← get)
    | throwError "incomplete_closure:E8.family_source_substitution"
  debit work
  return result

private def instantiate (body : Expr) (parameters : Array Expr) : M Expr := do
  let mut value := body
  for parameter in parameters.reverse do value ← substitute value parameter
  return value

private def telescope (initial : Expr) : M (Array FamilySourceBinder) := do
  let mut current := initial
  let mut result := #[]
  while let .forallE n d b bi := current do
    debit
    if result.size ≥ 64 then throwError "incomplete_closure:E8.family_source_binders"
    result := result.push { name := n, info := bi, domain := d }
    current := b
  return result

private def atPath (initial : Expr) (path : Array String) : M FamilySourceOccurrence := do
  if path.size > 256 then throwError "incomplete_closure:E8.family_source_path"
  let mut e := initial
  let mut context := #[]
  for step in path do
    debit
    e ← match e, step with
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | .forallE _ d _ _, "domain" | .lam _ d _ _, "domain" => pure d
      | .forallE n d b bi, "body" =>
        context := context.push { name := n, info := bi, domain := d }
        pure b
      | .lam n d b bi, "body" =>
        context := context.push { name := n, info := bi, domain := d, kind := "lambda" }
        pure b
      | .letE _ t _ _ _, "type" => pure t
      | .letE _ _ v _ _, "value" => pure v
      | .letE n t v b nd, "body" =>
        context := context.push {
          name := n, info := .default, domain := t, kind := "let", value := some v, nondep := nd }
        pure b
      | .proj _ _ b, "body" | .mdata _ b, "body" => pure b
      | _, _ => throwError "unclassified_form:family.source.absent_occurrence"
  return { path, context, raw := e }

/-- Closing retains binder kind, raw domain, let value and nondependency bit. -/
def close (context : Array FamilySourceBinder) (e : Expr) : Expr :=
  context.foldr (fun b e =>
    if b.kind == "lambda" then .lam b.name b.domain e b.info
    else if b.kind == "let" then .letE b.name b.domain (b.value.getD (.sort .zero)) e b.nondep
    else .forallE b.name b.domain e b.info) e

-- Classification may reduce aliases for typing, but the retained source,
-- domains and occurrences always come from the raw traversal above.
private partial def dictionaryType (type : Expr) (depth : Nat := 0) : M Bool := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.family_dictionary_depth"
  -- Dictionary status is semantic, independent of a definition's reducibility
  -- hint. Only this classifier reduces with full transparency; its result never
  -- replaces the raw source domains or occurrences, and uses the same budget.
  let type ← withTransparency .all <| whnf type
  match type with
  | .forallE n domain body bi =>
    fun fuel => withLocalDecl n bi domain fun x =>
      (do dictionaryType (← substitute body x) (depth + 1)).run fuel
  | _ => pure (Lean.isClass (← getEnv) (type.getAppFn.constName?.getD .anonymous))

private partial def classify (slots : Array Nat) (type : Expr) (i : Nat := 0) : M Unit := do
  debit
  if i > 64 then throwError "incomplete_closure:E8.family_source_binders"
  match type with
  | .forallE n domain body bi =>
    if slots.contains i then
      let dictionary ← dictionaryType domain
      if bi == .instImplicit || dictionary then
        throwError "unclassified_form:family.map.dictionary_coordinate"
      if domain == mkSort .zero || (← isProp domain) then
        throwError "unclassified_form:family.map.proof_coordinate"
    fun fuel => withLocalDecl n bi domain fun x => (do
      classify slots (← substitute body x) (i + 1)).run fuel
  | _ => pure ()

private def resolveM (info : ConstantInfo) (selection : FamilySourceSelection) : M FamilySourceScope := do
  let telescope ← telescope info.type
  let slots := selection.coordinates
  if slots.size > 64 then throwError "incomplete_closure:E8.family_source_coordinates"
  let mut previous : Option Nat := none
  let mut coordinateDomains := #[]
  for i in slots do
    debit
    unless i < telescope.size && previous.all (· < i) do
      throwError "unclassified_form:family.map.order_or_bounds"
    let binder := telescope[i]!
    let domain ← transform (slots.filter (· < i)) i binder.domain
    coordinateDomains := coordinateDomains.push { binder with domain }
    previous := some i
  classify slots info.type
  let state ← atPath info.type selection.statePath
  let output ← atPath info.type selection.outputPath
  -- Positional equality alone is insufficient: a nested binder reached inside
  -- an earlier domain is not a later source coordinate, even with equal type.
  for occurrence in #[state, output] do
    for coordinate in slots do
      unless occurrence.path.size > coordinate &&
          (occurrence.path.extract 0 (coordinate + 1)).all (· == "body") &&
          occurrence.context[coordinate]? == telescope[coordinate]? do
        throwError "unclassified_form:family.source.captured_coordinate"
  let stateFiber ← transform slots state.context.size state.raw
  let outputFiber ← transform slots output.context.size output.raw
  unless (← transform slots state.context.size stateFiber true).equal state.raw &&
      (← transform slots output.context.size outputFiber true).equal output.raw do
    throwError "unclassified_form:family.source.inverse_embedding"
  return {
    selection, sourceType := info.type, levels := info.levelParams, telescope, state, output, coordinateDomains, stateFiber, outputFiber }

def resolve (info : ConstantInfo) (selection : FamilySourceSelection) (fuel : Nat := 524288) :
    MetaM (FamilySourceScope × Nat) := withCumulativeBudget do
  let limit := min fuel 524288
  let (scope, remaining) ← (resolveM info selection).run limit
  return (scope, limit - remaining)

/-- Persistent source data is compared with a fresh raw traversal, before any
kernel equality is used to connect it to the actual signature fields. -/
def validate (info : ConstantInfo) (scope : FamilySourceScope) (fuel : Nat := 524288) :
    MetaM Nat := do
  let (current, work) ← resolve info scope.selection fuel
  unless current == scope do throwError "unclassified_form:family.source.stale_scope"
  return work

private partial def packedType (domains : Array FamilySourceBinder) (i : Nat)
    (parameters : Array Expr) : M Expr := do
  debit
  if i ≥ domains.size then return mkConst ``Unit
  let domain ← instantiate domains[i]!.domain parameters
  if i + 1 == domains.size then return domain
  fun fuel => withLocalDecl domains[i]!.name domains[i]!.info domain fun x => (do
    let tail ← packedType domains (i + 1) (parameters.push x)
    mkAppM ``Sigma #[← mkLambdaFVars #[x] tail]).run fuel

private partial def packedValue (type : Expr) (parameters : Array Expr) (i : Nat) : M Expr := do
  debit
  if i ≥ parameters.size then return mkConst ``Unit.unit
  if i + 1 == parameters.size then return parameters[i]!
  let args := type.getAppArgs
  if type.isAppOfArity ``Prod 2 then
    return ← mkAppM ``Prod.mk #[parameters[i]!, ← packedValue args[1]! parameters (i + 1)]
  if type.isAppOfArity ``Sigma 2 then
    let tailType ← whnf (mkApp args[1]! parameters[i]!)
    return ← mkAppOptM ``Sigma.mk #[some args[0]!, some args[1]!, some parameters[i]!,
      some (← packedValue tailType parameters (i + 1))]
  throwError "unclassified_form:family.source.packing"

private partial def fields (scope : FamilySourceScope) (signature thetaType : Expr)
    (i : Nat := 0) (parameters : Array Expr := #[]) : M Unit := do
  debit
  if i < scope.coordinateDomains.size then
    let binder := scope.coordinateDomains[i]!
    let domain ← instantiate binder.domain parameters
    fun fuel => withLocalDecl binder.name binder.info domain fun x =>
      (fields scope signature thetaType (i + 1) (parameters.push x)).run fuel
  else
    let theta ← packedValue thetaType parameters 0
    let state ← instantiate scope.stateFiber parameters
    let output ← instantiate scope.outputFiber parameters
    checkWithKernel state
    checkWithKernel output
    unless (← isType state) && (← isType output) do
      throwError "unclassified_form:family.source.not_type"
    let actualState ← mkAppM ``DependentFamily.Signature.State #[signature, theta]
    unless ← isDefEq state actualState do throwError "unclassified_form:family.source.state_fiber"
    let role ← mkAppM ``DependentFamily.Signature.Role #[signature]
    fun fuel => withLocalDeclD `role role fun role => (do
      debit
      let actualOutput ← mkAppM ``DependentFamily.Signature.Output #[signature, role, theta]
      unless ← isDefEq output actualOutput do
        throwError "unclassified_form:family.source.output_fiber").run fuel

/-- Kernel typing connects raw extracted fibers to the actual interface fields.
The packing is constructed from the dependency-closed source map; callers cannot
substitute an unrelated Θ or a Bool proxy for State. Every role is checked. -/
def validateFields (scope : FamilySourceScope) (signature : Expr) (fuel : Nat := 524288) :
    MetaM Nat := do
  let limit := min fuel 524288
  let action : M Unit := do
    let thetaType ← packedType scope.coordinateDomains 0 #[]
    let actualTheta ← mkAppM ``DependentFamily.Signature.Θ #[signature]
    unless ← isDefEq thetaType actualTheta do throwError "unclassified_form:family.source.theta:expected={thetaType}; actual={← whnf actualTheta}"
    fields scope signature thetaType
  let (_, remaining) ← action.run limit
  return limit - remaining

end LeanInformationAudit.FamilySource
