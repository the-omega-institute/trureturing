import LeanInformationAudit.Contract.FibSource

namespace LeanInformationAudit.FibFinite
open Lean CompiledSourceScope FibSource

/-- Acquisition is a constructor-data reader. It never invokes native code,
Lean evaluation, a theorem proof, a recursive author definition or an arbitrary
recursor. Finite vectors are indexed directly in their literal constructor tree. -/
private partial def dataHead (e : Expr) (depth : Nat := 0) : FibSource.M Expr := do
  debit
  if depth > 256 then fail "fib.acquisition_data_depth"
  let child := fun e => dataHead e (depth + 1)
  match e with
  | .mdata _ body => child body
  | .letE _ _ value body _ => child (body.instantiate1 value)
  | .const name levels =>
    if #[`Matrix.vecCons, `Matrix.vecEmpty].contains name then return e
    match ← getConstInfo name with
    | .defnInfo info =>
      if info.safety != .safe || (← read).recursive name ||
          (← read).implementedBy name || (← read).extern name then
        fail s!"fib.acquisition_unsupported_definition:{name}"
      unless levels.length == info.levelParams.length do fail "fib.acquisition_universes"
      child (info.value.instantiateLevelParams info.levelParams levels)
    | _ => return e
  | .proj name index base =>
    let base ← child base
    let .ctorInfo info ← getConstInfo (base.getAppFn.constName?.getD .anonymous)
      | fail "fib.acquisition_projection"
    unless info.induct == name && index < info.numFields &&
        base.getAppArgs.size == info.numParams + info.numFields do fail "fib.acquisition_projection"
    child base.getAppArgs[info.numParams + index]!
  | .app .. =>
    let mut fn ← child e.getAppFn
    let mut args := e.getAppArgs
    while let .lam _ _ body _ := fn do
      let some arg := args[0]? | return fn
      args := args.extract 1 args.size
      fn ← child (body.instantiate1 arg)
    let result := mkAppN fn args
    if fn.isApp && !args.isEmpty then return ← child result
    let some name := fn.constName? | return result
    let info ← getConstInfo name
    if let .recInfo recursor := info then
      -- Constructor cases are the only supported decoder computation. Recursive
      -- arithmetic and author folds are deliberately not acquisition formats.
      unless #[``Bool.rec, ``Option.rec, ``PUnit.rec, ``Prod.rec,
          ``Sigma.rec, ``Subtype.rec, ``Fin.rec, `LeanInformationAudit.Analysis.Value.rec].contains name do
        fail s!"fib.acquisition_unsupported_recursor:{name}"
      let some major := args[recursor.getMajorIdx]? | return result
      let major ← child major
      let some ctor := major.getAppFn.constName? | fail "fib.acquisition_decoder_neutral"
      let .ctorInfo layout ← getConstInfo ctor | fail "fib.acquisition_decoder_constructor"
      let some rule := recursor.rules.find? (·.ctor == ctor) | fail "fib.acquisition_decoder_case"
      unless rule.nfields == layout.numFields &&
          major.getAppNumArgs == layout.numParams + layout.numFields do
        fail "fib.acquisition_decoder_layout"
      let leading := args.extract 0 (recursor.numParams + recursor.numMotives + recursor.numMinors)
      let fields := major.getAppArgs.extract layout.numParams major.getAppNumArgs
      let suffix := args.extract (recursor.getMajorIdx + 1) args.size
      child (mkAppN (rule.rhs.instantiateLevelParams recursor.levelParams fn.constLevels!)
        (leading ++ fields ++ suffix))
    else return result
  | .mvar _ | .bvar _ | .fvar _ => fail "fib.acquisition_open_data"
  | _ => return e

private def applyRole (fn role : Expr) : FibSource.M Expr := dataHead (mkApp fn role)

private partial def vectorAt (fn : Expr) (index : Nat) (depth : Nat := 0) : FibSource.M Expr := do
  debit
  if depth > 256 then fail "fib.acquisition_vector_depth"
  let fn ← dataHead fn
  match fn with
  | .lam _ _ body _ =>
    unless !body.hasLooseBVars do fail "fib.acquisition_function_requires_computation"
    dataHead body
  | _ =>
    unless fn.isAppOfArity `Matrix.vecCons 4 do fail "fib.acquisition_requires_literal_vector"
    if index == 0 then dataHead fn.getAppArgs[2]!
    else vectorAt fn.getAppArgs[3]! (index - 1) (depth + 1)

private partial def list (term : Expr) (depth : Nat := 0) : FibSource.M (Array Expr) := do
  debit
  if depth > 256 then fail "fib.acquisition_enumeration_limit"
  let term ← dataHead term
  if term.isAppOfArity ``List.nil 1 then return #[]
  unless term.isAppOfArity ``List.cons 3 do fail "fib.acquisition_requires_literal_list"
  return #[term.getAppArgs[1]!] ++ (← list term.getAppArgs[2]! (depth + 1))

private partial def valueJson (value : Expr) (depth : Nat := 0) : FibSource.M Json := do
  debit
  if depth > 64 then fail "fib.acquisition_value_depth"
  let value ← dataHead value
  let args := value.getAppArgs
  let head := value.getAppFn.constName?.getD .anonymous
  let base := `LeanInformationAudit.Analysis.Value
  if #[base ++ `unit, base ++ `none].contains head && args.isEmpty then
    return Json.mkObj [("kind", toJson head.getString!)]
  if head == base ++ `pair && args.size == 2 then
    return Json.mkObj [("kind", toJson "pair"),
      ("first", ← valueJson args[0]! (depth + 1)), ("second", ← valueJson args[1]! (depth + 1))]
  unless args.size == 1 do fail "fib.acquisition_value_constructor"
  let atom ← dataHead args[0]!
  let content ← if head == base ++ `bool then
      toJson <$> IO.ofExcept (Contract.Literal.bool "fib.value" atom)
    else if head == base ++ `nat then
      toJson <$> IO.ofExcept (Contract.Literal.nat "fib.value" atom)
    else if head == base ++ `int then
      toJson <$> IO.ofExcept (Contract.Literal.int "fib.value" atom)
    else if head == base ++ `text then
      toJson <$> IO.ofExcept (Contract.Literal.string "fib.value" atom)
    else if head == base ++ `some then valueJson atom (depth + 1)
    else fail "fib.acquisition_value_constructor"
  return Json.mkObj [("kind", toJson head.getString!), ("value", content)]

private def matrix (fn : Expr) (n : Nat) : FibSource.M Json := do
  let rows ← (List.range n).toArray.mapM fun i => do
    let row ← vectorAt fn i
    (List.range n).toArray.mapM fun j => do
      IO.ofExcept (Contract.Literal.bool "fib.kernel" (← vectorAt row j))
  return toJson rows

private def decoded (decoder role value : Expr) : FibSource.M Json := do
  let result ← dataHead (mkApp2 decoder role value)
  unless result.isAppOfArity ``Option.some 2 do fail "fib.acquisition_output_decode"
  let actual ← dataHead result.getAppArgs[1]!
  -- Preserve the decoded constructor, never equate display codes to observations.
  let head := actual.getAppFn.constName?.getD .anonymous
  if !actual.isLit then
    let .ctorInfo _ ← getConstInfo head | fail "fib.acquisition_output_not_constructor"
  let literal := match actual with
    | .lit (.natVal n) => Json.mkObj [("kind", toJson "nat"), ("value", toJson n)]
    | .lit (.strVal s) => Json.mkObj [("kind", toJson "text"), ("value", toJson s)]
    | _ => if actual.isConstOf ``Bool.true || actual.isConstOf ``Bool.false then
        Json.mkObj [("kind", toJson "bool"), ("value", toJson (actual.isConstOf ``Bool.true))]
      else Json.null
  return Json.mkObj [("constructor", toJson head.toString), ("term", describe actual),
    ("literal", literal), ("syntax", toJson (reprStr actual))]

/-- Proof fields remain opaque. Their compiled types tie these exact data fields
to complete/nodup states, decoded outputs, both kernel directions and every layer. -/
def acquire (bound : Bound) (domain presentation : Expr) : FibSource.M Json := do
  let scope ← dataHead (← projectField `LeanInformationAudit.Analysis.Domain.scope domain)
  let scopeName := scope.getAppFn.constName?.getD .anonymous
  let mut scopeKind := ""
  for kind in ["whole", "restriction", "quotient"] do
    if scopeName == (`LeanInformationAudit.Analysis.DomainScope).str kind then scopeKind := kind
  if scopeKind.isEmpty then fail "fib.acquisition_domain_scope"
  let enum ← projectField `LeanInformationAudit.Analysis.FinitePresentation.enumeration presentation
  let states ← list (← projectField
    `D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration.states enum)
  let values ← projectField `LeanInformationAudit.Analysis.FinitePresentation.values presentation
  let decoder ← projectField `LeanInformationAudit.Analysis.FinitePresentation.decode presentation
  let kernels ← projectField `LeanInformationAudit.Analysis.FinitePresentation.kernel presentation
  let task ← projectField `LeanInformationAudit.Analysis.FinitePresentation.taskValues presentation
  let layers ← projectField `LeanInformationAudit.Analysis.FinitePresentation.layers presentation
  let outputs ← bound.roles.mapM fun role => do
    let rows ← applyRole values role
    (List.range states.size).toArray.mapM fun index => do
      let value ← vectorAt rows index
      return Json.mkObj [("value", ← valueJson value), ("decoded", ← decoded decoder role value)]
  let taskOutputs ← (List.range states.size).toArray.mapM fun index => do
    let value ← vectorAt task index
    return Json.mkObj [("value", ← valueJson value),
      ("decoded", ← decoded decoder bound.roles[bound.task]! value)]
  let relations ← bound.roles.mapM fun role => do matrix (← applyRole kernels role) states.size
  let layerRelations ← (List.range (bound.additions.size + 1)).toArray.mapM fun i => do
    matrix (← vectorAt layers i) states.size
  let mut certificates : List (String × Json) := []
  for field in ["values_correct", "kernel_correct", "task_correct", "layers_correct"] do
    let proof ← projectField ((`LeanInformationAudit.Analysis.FinitePresentation).str field) presentation
    certificates := certificates ++ [(field, describe (← projectType proof))]
  for field in ["nodup", "complete"] do
    let proof ← projectField
      ((`D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration).str field) enum
    certificates := certificates ++ [(field, describe (← projectType proof))]
  return Json.mkObj [
    ("cardinality", toJson states.size), ("scope", toJson scopeKind),
    ("parameter", describe (← dataHead
      (← projectField `LeanInformationAudit.Analysis.Domain.parameter domain))),
    ("state_type", describe (← dataHead
      (← projectField `LeanInformationAudit.Analysis.Domain.State domain))),
    ("domain", describe domain), ("scope_evidence", describe scope),
    ("states", toJson (states.map describe)), ("outputs", toJson outputs),
    ("task_outputs", toJson taskOutputs), ("kernels", toJson relations),
    ("layers", toJson layerRelations), ("certificates", Json.mkObj certificates)]

/-- Finite acquisition failure leaves the complete source/plan binding intact. -/
def request (bound : Bound) : FibSource.M Json := do
  let base := `LeanInformationAudit.Analysis.Acquisition
  let mut finite := Json.null
  let mut parameter := Json.null
  let mut kind := "unavailable"
  let mut reason := ""
  try
    let acquisition ← dataHead bound.acquisition
    let head := acquisition.getAppFn.constName?.getD .anonymous
    if head == base ++ `unavailable then
      let fs ← fields (base ++ `unavailable) acquisition
      reason ← IO.ofExcept (Contract.Literal.string "fib.acquisition_reason" (← dataHead fs[0]!))
    else if head == base ++ `infinite then
      let fs ← fields (base ++ `infinite) acquisition
      kind := "infinite"
      parameter := describe fs[0]!
      reason := "certified infinite selected parameter fiber; no finite pair denominator"
    else if head == base ++ `finite then
      let fs ← fields (base ++ `finite) acquisition
      unless bound.planReason.isEmpty do fail bound.planReason
      finite ← acquire bound fs[0]! fs[1]!
      kind := "finite"
    else reason := "fib.acquisition_constructor_unavailable"
  catch error => reason := error.toString
  if !bound.planReason.isEmpty && kind != "infinite" then
    kind := "unavailable"
    reason := bound.planReason
  return Json.mkObj [
    ("arena", toJson "typed-source"), ("binding", bound.binding), ("plan", planJson bound),
    ("acquisition", Json.mkObj [("kind", toJson kind), ("reason", toJson reason),
      ("parameter", parameter)]), ("finite", finite)]

end LeanInformationAudit.FibFinite
