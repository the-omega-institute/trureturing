import Lean.Declaration
import Lean.LocalContext
import Lean.Util.InstantiateLevelParams

namespace LeanInformationAudit.TemplateAudit
open Lean

/-- Compiler-owned typing placeholder; never a delivered kernel proof. -/
def proofPlaceholder (type : Expr) : Expr := mkApp (mkConst ``lcProof) type

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.Contract.CompiledExpressions
open Lean

/-- Read-only compiler declarations and lexical binder data. Type-shape queries
assume compiler-checked terms; they do not validate operands or check proofs. -/
structure Context where
  find : Name → Option ConstantInfo
  local? : FVarId → Option LocalDecl := fun _ => none
  heartbeatStart : Nat
  heartbeatLimit : Nat

private structure WorkState where
  remaining : Nat
  heads : Std.HashMap (ExprStructEq × Bool × Bool) Expr := {}
  types : Std.HashMap (ExprStructEq × Array ExprStructEq) Expr := {}
  erased : Std.HashMap (ExprStructEq × Array ExprStructEq) Expr := {}
  comparisons : Std.HashMap (ExprStructEq × ExprStructEq × Array ExprStructEq) Bool := {}

abbrev M := ReaderT Context (StateT WorkState IO)

private def step (depth : Nat) : M Unit := do
  if depth > 256 then throw <| IO.userError "incomplete_closure:E8.compiled_expression_depth"
  let remaining := (← get).remaining
  if remaining == 0 then throw <| IO.userError "incomplete_closure:E8.erasure_work"
  modify fun state => { state with remaining := remaining - 1 }
  let context ← read
  if context.heartbeatLimit != 0 &&
      (← IO.getNumHeartbeats) - context.heartbeatStart > context.heartbeatLimit then
    throw <| IO.userError "incomplete_closure:E8.compiled_expression_heartbeats"

private def constant (name : Name) : M ConstantInfo := do
  let some info := (← read).find name
    | throw <| IO.userError s!"incomplete_closure:E7.compiled_constant:{name}"
  return info

mutual
/-- Administrative reduction of compiler terms. Opaque proof implementations
stay opaque. Recursor rules and projection layouts are compiler data. -/
partial def head (e : Expr) (depth : Nat := 0) (zeta : Bool := true)
    (preserveDecisions : Bool := false) : M Expr := do
  step depth
  let key := (ExprStructEq.mk e, zeta, preserveDecisions)
  if let some value := (← get).heads[key]? then return value
  let value ← headCore e depth zeta preserveDecisions
  modify fun state => { state with heads := state.heads.insert key value }
  return value

private partial def headCore (e : Expr) (depth : Nat := 0) (zeta : Bool := true)
    (preserveDecisions : Bool := false) : M Expr := do
  if preserveDecisions && e.isAppOfArity ``Decidable.decide 2 then return e
  let child := fun e => head e (depth + 1) zeta preserveDecisions
  match e with
  | .mdata _ body => child body
  | .letE _ _ value body _ => if zeta then child (body.instantiate1 value) else pure e
  | .const name levels =>
    match ← constant name with
    | .defnInfo info =>
      unless info.safety == .safe && levels.length == info.levelParams.length do
        throw <| IO.userError s!"unclassified_form:E7.compiled_definition:{name}"
      child (info.value.instantiateLevelParams info.levelParams levels)
    | _ => return e
  | .fvar id =>
    let some binder := (← read).local? id
      | throw <| IO.userError s!"incomplete_closure:E7.compiled_local:{id.name}"
    if let some value := binder.value? then
      if zeta then child value else pure e
    else pure e
  | .app .. =>
    let fn ← child e.getAppFn
    let mut args := e.getAppArgs
    let mut fn := fn
    while let .lam _ _ body _ := fn do
      step depth
      let some argument := args[0]? | return fn
      args := args.extract 1 args.size
      fn ← child (body.instantiate1 argument)
    let result := mkAppN fn args
    let .const name levels := fn | return result
    let description ← constant name
    if let .quotInfo quotient := description then
      if quotient.kind matches .lift then
        let some major := args[5]? | return result
        let major ← child major
        let .const ctor _ := major.getAppFn | return result
        let .quotInfo constructor ← constant ctor | return result
        unless (constructor.kind matches .ctor) && major.getAppNumArgs == 3 do return result
        child <| mkAppN (mkApp args[3]! major.getAppArgs[2]!) (args.extract 6 args.size)
      else return result
    else
      let .recInfo recursor := description | return result
      let some major := args[recursor.getMajorIdx]? | return result
      let major ← child major
      let (ctor, fields) ← match major with
        | .lit (.natVal n) =>
          if n == 0 then pure (``Nat.zero, #[]) else pure (``Nat.succ, #[mkNatLit (n - 1)])
        | _ => do
          let .const ctor _ := major.getAppFn | return result
          let .ctorInfo info ← constant ctor | return result
          unless major.getAppArgs.size == info.numParams + info.numFields do
            throw <| IO.userError s!"incomplete_closure:E7.compiled_constructor:{ctor}"
          pure (ctor, major.getAppArgs.extract info.numParams major.getAppArgs.size)
      let some rule := recursor.rules.find? (·.ctor == ctor) | return result
      unless rule.nfields == fields.size && levels.length == recursor.levelParams.length do
        throw <| IO.userError s!"incomplete_closure:E7.compiled_recursor:{name}"
      let leading := args.extract 0 (recursor.numParams + recursor.numMotives + recursor.numMinors)
      let suffix := args.extract (recursor.getMajorIdx + 1) args.size
      child <| mkAppN (rule.rhs.instantiateLevelParams recursor.levelParams levels)
        (leading ++ fields ++ suffix)
  | .proj name index value =>
    let value ← child value
    let .const ctor _ := value.getAppFn | return .proj name index value
    let .ctorInfo info ← constant ctor | return .proj name index value
    unless info.induct == name && index < info.numFields do
      throw <| IO.userError s!"incomplete_closure:E7.compiled_projection:{name}"
    let some field := value.getAppArgs[info.numParams + index]?
      | throw <| IO.userError s!"incomplete_closure:E7.compiled_projection_field:{name}:{index}"
    child field
  | _ => return e

end

/-- Project declaration types through their already compiled application spine.
No argument is compared with a domain, and no proof body is inferred or checked. -/
partial def typeShape (e : Expr) (binders : Array Expr := #[])
    (depth : Nat := 0) : M Expr := do
  step depth
  let key := (ExprStructEq.mk e, binders.map ExprStructEq.mk)
  if let some value := (← get).types[key]? then return value
  let value ← typeShapeCore e binders depth
  modify fun state => { state with types := state.types.insert key value }
  return value

where typeShapeCore (e : Expr) (binders : Array Expr) (depth : Nat) : M Expr := do
  let child := fun e => typeShape e binders (depth + 1)
  match e with
  | .const name levels =>
    let info ← constant name
    unless levels.length == info.levelParams.length do
      throw <| IO.userError s!"incomplete_closure:E7.compiled_universes:{name}"
    return info.type.instantiateLevelParams info.levelParams levels
  | .fvar id =>
    let some binder := (← read).local? id
      | throw <| IO.userError s!"incomplete_closure:E7.compiled_local:{id.name}"
    return binder.type
  | .bvar index =>
    unless index < binders.size do
      throw <| IO.userError "incomplete_closure:E7.open_expression"
    return binders[binders.size - 1 - index]!.liftLooseBVars 0 (index + 1)
  | .sort level => return .sort (.succ level)
  | .lit (.natVal _) => return mkConst ``Nat
  | .lit (.strVal _) => return mkConst ``String
  | .app .. =>
    let mut type ← child e.getAppFn
    for argument in e.getAppArgs do
      step depth
      let .forallE _ _ body _ ← head type (depth + 1)
        | throw <| IO.userError s!"incomplete_closure:E7.compiled_application_type:{repr e}; type={repr type}"
      type := body.instantiate1 argument
    return type
  | .lam name domain body info =>
    let result ← typeShape body (binders.push domain) (depth + 1)
    return .forallE name domain result info
  | .forallE _ domain body _ =>
    let .sort v ← head (← typeShape body (binders.push domain) (depth + 1)) (depth + 1)
      | throw <| IO.userError "incomplete_closure:E7.compiled_body_sort"
    -- For a compiler-checked proposition, imax u 0 = 0. The domain's
    -- declaration is still inspected by provenance; its sort adds no result data.
    if v.isZero then return mkSort .zero
    let .sort u ← head (← child domain) (depth + 1)
      | throw <| IO.userError "incomplete_closure:E7.compiled_domain_sort"
    return .sort ((Level.imax u v).normalize)
  | .letE _ _ value body _ => child (body.instantiate1 value)
  | .mdata _ body => child body
  | .proj name index value =>
    let baseType ← head (← child value) (depth + 1)
    unless baseType.getAppFn.isConstOf name do
      throw <| IO.userError s!"incomplete_closure:E7.compiled_projection_type:{name}"
    let .inductInfo shape ← constant name
      | throw <| IO.userError s!"incomplete_closure:E7.compiled_inductive:{name}"
    let [ctor] := shape.ctors
      | throw <| IO.userError s!"incomplete_closure:E7.compiled_structure:{name}"
    let .ctorInfo description ← constant ctor
      | throw <| IO.userError s!"incomplete_closure:E7.compiled_constructor:{ctor}"
    let levels := baseType.getAppFn.constLevels!
    unless levels.length == description.levelParams.length && index < description.numFields do
      throw <| IO.userError s!"incomplete_closure:E7.compiled_projection_layout:{name}"
    let mut type := description.type.instantiateLevelParams description.levelParams levels
    for parameter in baseType.getAppArgs.extract 0 description.numParams do
      step depth
      let .forallE _ _ body _ ← head type (depth + 1)
        | throw <| IO.userError s!"incomplete_closure:E7.compiled_structure_parameters:{name}"
      type := body.instantiate1 parameter
    for previous in [:index] do
      step depth
      let .forallE _ _ body _ ← head type (depth + 1)
        | throw <| IO.userError s!"incomplete_closure:E7.compiled_structure_fields:{name}"
      type := body.instantiate1 (.proj name previous value)
    let .forallE _ domain _ _ ← head type (depth + 1)
      | throw <| IO.userError s!"incomplete_closure:E7.compiled_projection_domain:{name}"
    return domain
  | .mvar _ => throw <| IO.userError "incomplete_closure:E7.metavariable"

/-- Classify a compiler-checked type's proposition sort. A forall is Prop
exactly when its body is Prop; domain universe magnitudes do not affect this
classification. Domain syntax remains an independent provenance input. -/
partial def propositionShape (type : Expr) (binders : Array Expr := #[])
    (depth : Nat := 0) : M Bool := do
  step depth
  match type with
  | .forallE _ domain body _ => propositionShape body (binders.push domain) (depth + 1)
  | .letE _ _ value body _ => propositionShape (body.instantiate1 value) binders (depth + 1)
  | .mdata _ body => propositionShape body binders (depth + 1)
  | _ => return (← head (← typeShape type binders (depth + 1)) (depth + 1)).isProp

mutual
/-- Compare compiled data terms after bounded administrative computation.
The comparison consumes declaration syntax and never invokes a type checker.
Binder annotations are compared by the source reconstruction consumer. -/
partial def sameShape (left right : Expr) (depth : Nat := 0)
    (binders : Array Expr := #[]) : M Bool := do
  step depth
  if left == right then return true
  let key := (ExprStructEq.mk left, ExprStructEq.mk right, binders.map ExprStructEq.mk)
  if let some value := (← get).comparisons[key]? then return value
  let value ← sameShapeCore left right depth binders
  modify fun state => { state with comparisons := state.comparisons.insert key value }
  return value

private partial def sameShapeCore (left right : Expr) (depth : Nat := 0)
    (binders : Array Expr := #[]) : M Bool := do
  if left == right then return true
  let child := fun a b => sameShape a b (depth + 1) binders
  -- Matching compiled heads can be compared by congruence before expanding
  -- their mathematical implementations. A miss still uses administrative reduction.
  let congruent : M Bool := do match left, right with
    | .app .., .app .. => do
      unless left.getAppFn.equal right.getAppFn &&
          left.getAppNumArgs == right.getAppNumArgs do return false
      for (a, b) in left.getAppArgs.zip right.getAppArgs do
        unless ← child a b do return false
      return true
    | .lam _ t b _, .lam _ u c _ | .forallE _ t b _, .forallE _ u c _ =>
      unless ← child t u do return false
      sameShape b c (depth + 1) (binders.push t)
    | .const a us, .const b vs =>
      pure (a == b && us.map Level.normalize == vs.map Level.normalize)
    | .sort a, .sort b => pure (a.normalize == b.normalize)
    | .proj n i b, .proj m j c =>
      unless n == m && i == j do return false
      child b c
    | _, _ => pure false
  if ← congruent then return true
  -- Compiled proof terms are compared through their propositions. No proof
  -- implementation is read or checked, including for proof-valued class fields.
  let leftType ← typeShape left binders
  if ← propositionShape leftType binders (depth + 1) then
    let rightType ← typeShape right binders
    if ← propositionShape rightType binders (depth + 1) then
      return ← sameShape leftType rightType (depth + 1) binders
  let left ← head left depth (preserveDecisions := true)
  let right ← head right depth (preserveDecisions := true)
  if left == right then return true
  -- Decidable dictionaries for the same proposition determine the same Bool.
  -- Reification compares that proposition without running or synthesizing a dictionary.
  if left.isAppOfArity ``Decidable.decide 2 && right.isAppOfArity ``Decidable.decide 2 then
    return ← sameShape left.getAppArgs[0]! right.getAppArgs[0]! (depth + 1) binders
  let compare := fun a b => sameShape a b (depth + 1) binders
  match left, right with
  | .sort a, .sort b => return a.normalize == b.normalize
  | .const a us, .const b vs =>
    return a == b && us.map Level.normalize == vs.map Level.normalize
  | .app f a, .app g b =>
    unless ← compare f g do return false
    compare a b
  | .lam _ t b _, .lam _ u c _ | .forallE _ t b _, .forallE _ u c _ =>
    unless ← compare t u do return false
    sameShape b c (depth + 1) (binders.push t)
  | .proj n i b, .proj m j c =>
    unless n == m && i == j do return false
    compare b c
  | .lam _ domain body _, function =>
    let .forallE _ functionDomain _ _ ← head (← typeShape function binders)
      | return false
    unless ← compare domain functionDomain do return false
    sameShape body (mkApp (function.liftLooseBVars 0 1) (.bvar 0)) (depth + 1) (binders.push domain)
  | function, .lam _ domain body _ =>
    let .forallE _ functionDomain _ _ ← head (← typeShape function binders)
      | return false
    unless ← compare domain functionDomain do return false
    sameShape (mkApp (function.liftLooseBVars 0 1) (.bvar 0)) body (depth + 1) (binders.push domain)
  | .lit (.natVal 0), .const ``Nat.zero [] | .const ``Nat.zero [], .lit (.natVal 0) =>
    return true
  | .lit (.natVal n), .app (.const ``Nat.succ []) tail =>
    unless n > 0 do return false
    compare (mkNatLit (n - 1)) tail
  | .app (.const ``Nat.succ []) tail, .lit (.natVal n) =>
    unless n > 0 do return false
    compare tail (mkNatLit (n - 1))
  | _, _ => return false

end

private partial def erase (e : Expr) (binders : Array Expr := #[])
    (depth : Nat := 0) : M Expr := do
  step depth
  let key := (ExprStructEq.mk e, binders.map ExprStructEq.mk)
  if let some value := (← get).erased[key]? then return value
  let value ← eraseCore e binders depth
  modify fun state => { state with erased := state.erased.insert key value }
  return value

where eraseCore (e : Expr) (binders : Array Expr) (depth : Nat) : M Expr := do
  let type ← typeShape e binders depth
  if ← propositionShape type binders depth then
    return TemplateAudit.proofPlaceholder (← erase type binders (depth + 1))
  let child := fun e => erase e binders (depth + 1)
  match e with
  | .app f a => return .app (← child f) (← child a)
  | .lam name type body info =>
    return .lam name (← child type) (← erase body (binders.push type) (depth + 1)) info
  | .forallE name type body info =>
    return .forallE name (← child type) (← erase body (binders.push type) (depth + 1)) info
  | .letE name type value body nondep =>
    return .letE name (← child type) (← child value)
      (← erase body (binders.push type) (depth + 1)) nondep
  | .mdata data body => return .mdata data (← child body)
  | .proj name index value => return .proj name index (← child value)
  | .mvar _ => throw <| IO.userError "incomplete_closure:E7.metavariable"
  | _ => return e

/-- Run one bounded compiled-data calculation. All shape queries and reductions
share its original work quota and heartbeat boundary. -/
def run (context : Context) (action : M α) (fuel : Nat := 524288) : IO (α × Nat) := do
  let limit := min fuel 524288
  let (result, remaining) ← action.run context |>.run { remaining := limit }
  return (result, limit - remaining.remaining)

/-- Reflect the compiler's finite signature dictionary, retaining its declared
order. Only its index constructors are read; realizations are never enumerated. -/
def finiteIndices (dictionary : Expr) : M (Array Expr) := do
  let elems ← head (.proj `Fintype 0 dictionary)
  let multiset ← head (.proj `Finset 0 elems)
  unless multiset.isAppOfArity ``Quot.mk 3 do
    throw <| IO.userError "contract.cannot_decode:partial_sensitivity:finite_index_dictionary"
  let mut pending := multiset.getArg! 2
  let mut indices := #[]
  repeat
    pending ← head pending
    if pending.isAppOfArity ``List.nil 1 then break
    unless pending.isAppOfArity ``List.cons 3 do
      throw <| IO.userError "contract.cannot_decode:partial_sensitivity:finite_index_list"
    indices := indices.push (pending.getArg! 1)
    pending := pending.getArg! 2
  return indices

/-- Read the obligation constructors selected by a compiled partial-slot family.
Compiler types supply the ULift layout, without operand validation or proof checking. -/
def partialSlotStates (fn dictionary : Expr) : M (Array Bool) := do
  let type ← head (← typeShape fn)
  let .forallE _ domain _ _ := type
    | throw <| IO.userError "contract.cannot_decode:partial_sensitivity:slot_function_type"
  let domain ← head domain
  unless domain.isAppOf ``ULift do
    throw <| IO.userError "contract.cannot_decode:partial_sensitivity:index_carrier"
  let slots ← finiteIndices dictionary
  slots.mapM fun index => do
    let lifted := mkAppN (mkConst ``ULift.up domain.getAppFn.constLevels!)
      (domain.getAppArgs.push index)
    let value ← head (mkApp fn lifted)
    let name := value.getAppFn.constName?.getD .anonymous
    if name == `LeanInformationAudit.Contract.Obligation.evidence then return true
    unless #[`LeanInformationAudit.Contract.Obligation.unsupported,
        `LeanInformationAudit.Contract.Obligation.unknown,
        `LeanInformationAudit.Contract.Obligation.absent].contains name do
      throw <| IO.userError "contract.cannot_decode:partial_sensitivity:slot_obligation"
    return false

/-- Preserve original syntax and charge declaration-type traversal to the same
fixed work quota as the proof-opaque expression walk. -/
def eraseProofs (context : Context) (e : Expr) (fuel : Nat := 524288) : IO (Expr × Nat) := do
  let limit := min fuel 524288
  let (result, remaining) ← erase e |>.run context |>.run { remaining := limit }
  return (result, limit - remaining.remaining)

end LeanInformationAudit.Contract.CompiledExpressions
