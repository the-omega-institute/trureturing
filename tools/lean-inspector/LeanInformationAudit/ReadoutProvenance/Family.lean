import Lean


namespace LeanInformationAudit.RegistrationGates.ReadoutFamily
open Lean

-- §10.1 budget record: safety limit outside the capacity domain; owner=governance lane;
-- date=2026-09-13; basis=the realization decoder's 256-step structural-depth
-- ceiling; exit condition=the supported realization encoding or pinned Lean
-- version changes, then rerun decoder depth and malformed-encoding fixtures.
-- Deeper or unrecognized encodings fail closed; shared fuel also bounds width.
private def depthLimit : Nat := 256

private inductive WeightNode where
  | expr (value : Expr)
  | level (value : Level)
  deriving BEq, Hashable, Inhabited

private structure Spine where
  head : Expr
  reversed : List Expr := []
  arity : Nat := 0
  deriving Inhabited

private structure WorkState where
  fuel : Nat
  cap : Nat
  spent : Nat := 0
  weights : Std.HashMap WeightNode Nat := {}
  spines : Std.HashMap Expr Spine := {}

private abbrev DecodeM := OptionT (StateM WorkState)

private def charge (amount : Nat := 1) : DecodeM Unit := do
  let s ← get
  unless amount ≤ s.fuel do failure
  modify fun s => { s with fuel := s.fuel - amount, spent := s.spent + amount }

private def weightChildren : WeightNode → DecodeM (Array WeightNode)
  | .expr e => do
    match e with
    | .app f a | .lam _ f a _ | .forallE _ f a _ => return #[.expr f, .expr a]
    | .letE _ t v b _ => return #[.expr t, .expr v, .expr b]
    | .mdata _ b | .proj _ _ b => return #[.expr b]
    | .sort l => return #[.level l]
    | .const _ levels =>
      let mut children := #[]
      for level in levels do
        charge
        children := children.push (.level level)
      return children
    | _ => return #[]
  | .level l => return match l with
    | .succ a => #[.level a]
    | .max a b | .imax a b => #[.level a, .level b]
    | _ => #[]

-- Iterative postorder avoids using the native stack for untrusted tree depth.
-- The capped tree weight is reused, while calculating it also consumes fuel.
private def weight (e : Expr) : DecodeM Nat := do
  let root := WeightNode.expr e
  let mut pending : List (WeightNode × Bool) := [(root, false)]
  while !pending.isEmpty do
    charge
    let (node, ready) := pending.head!
    pending := pending.tail!
    if (← get).weights.contains node then continue
    let children ← weightChildren node
    if ready then
      let mut size := 1
      for child in children do
        charge
        let some childSize := (← get).weights[child]? | failure
        size := min (← get).cap (size + childSize)
      modify fun s => { s with weights := s.weights.insert node size }
    else
      pending := (node, true) :: pending
      for child in children do
        charge
        pending := (child, false) :: pending
  let some size := (← get).weights[root]? | failure
  return size

-- Prefixes share a reversed argument list. Walking every family subexpression
-- therefore does not rescan the entire application spine at each prefix.
private def spine (e : Expr) : DecodeM Spine := do
  let mut current := e
  let mut pending : List (Expr × Expr) := []
  let mut result : Spine := { head := e }
  while true do
    charge
    if let some cached := (← get).spines[current]? then
      result := cached
      break
    match current with
    | .app f arg =>
      pending := (current, arg) :: pending
      current := f
    | _ =>
      result := { head := current }
      modify fun s => { s with spines := s.spines.insert current result }
      break
  for (application, arg) in pending do
    charge
    result := { result with reversed := arg :: result.reversed, arity := result.arity + 1 }
    modify fun s => { s with spines := s.spines.insert application result }
  return result

private def argument (s : Spine) (index : Nat) : DecodeM Expr := do
  unless index < s.arity do failure
  let offset := s.arity - 1 - index
  charge (offset + 1)
  let some arg := s.reversed[offset]? | failure
  return arg

private def applySpine (head : Expr) (s : Spine) : DecodeM Expr := do
  charge s.arity
  let mut result := head
  for arg in s.reversed.reverse do
    charge
    result := mkApp result arg
  return result

private def instantiate (body arg : Expr) : DecodeM Expr := do
  charge
  if !body.hasLooseBVars then return body
  let bodyWeight ← weight body
  let argWeight ← if arg.hasLooseBVars then weight arg else pure 0
  -- An open replacement can require lifting at every substituted occurrence.
  charge (bodyWeight * (argWeight + 1))
  return body.instantiate1 arg

private def instantiateLevels (body : Expr) (params : List Name) (levels : List Level) :
    DecodeM Expr := do
  charge
  if !body.hasLevelParam then return body
  let size ← weight body
  let mut factor := 1
  for _ in params do
    charge
    factor := factor + 1
  -- Each parameter occurrence may inspect the complete parameter substitution.
  charge (size * factor)
  return body.instantiateLevelParams params levels

private def beta (s : Spine) : DecodeM Expr := do
  let size ← weight s.head
  let mut factor := 1
  for arg in s.reversed do
    charge
    if arg.hasLooseBVars then factor := factor + (← weight arg)
  -- Reserve lambda/metadata scanning, substitution, and residual applications.
  charge (size + size * factor + s.arity)
  charge s.arity
  return s.head.betaRev s.reversed.toArray

private def recordHead (env : Environment) : Nat → Expr → DecodeM Expr
  | 0, _ => failure
  | depth + 1, e => do
    charge
    let s ← spine e
    match s.head with
    | .mdata _ body => recordHead env depth (← applySpine body s)
    | .letE _ _ value body _ =>
      recordHead env depth (← applySpine (← instantiate body value) s)
    | .lam .. =>
      if s.arity == 0 then return e
      recordHead env depth (← beta s)
    | .const name levels =>
      match env.find? name with
      | some (.defnInfo info) =>
        recordHead env depth (← applySpine (← instantiateLevels info.value info.levelParams levels) s)
      | some _ => return e
      | none => failure
    | .proj _ index value =>
      let value ← recordHead env depth value
      let constructor ← spine value
      let .const name _ := constructor.head | return e
      let some (.ctorInfo info) := env.find? name | return e
      let field ← argument constructor (info.numParams + index)
      recordHead env depth (← applySpine field s)
    | _ => return e

def carrierHeads : Array Name := #[
  `D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.Index,
  `D5.S3.ConceptDynamics.InformationEscape.Catalog.Index,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Index,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature.Output,
  `D5.S3.ConceptDynamics.InformationEscape.Arena.State,
  `LeanInformationAudit.StructuralPrimitiveSignature.Index,
  `LeanInformationAudit.StructuralPrimitiveSignature.Output,
  `LeanInformationAudit.StructuralArena.State,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralArena.State,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralPrimitiveSignature.Index,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralPrimitiveSignature.Output]

private def decode (env : Environment) (realization : Name) : DecodeM Expr := do
  charge
  let some info := env.find? realization | failure
  let root ← match info with
    | .thmInfo info => do
      let type ← recordHead env depthLimit info.type
      let s ← spine type
      unless s.arity == 3 && s.head.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization do failure
      argument s 2
    | .defnInfo _ => pure (mkConst realization)
    | _ => failure
  let value ← recordHead env depthLimit root
  let s ← spine value
  unless s.head.constName? == some `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.mk ||
      s.head.constName? == some `LeanInformationAudit.StructuralPrimitiveRealization.mk do failure
  argument s 2

/-- Decode a readout and return the work already debited from the supplied fuel.
The caller transfers this debit even when decoding fails; caches are query-local. -/
def extract (env : Environment) (realization : Name) (fuel : Nat) : Option (Expr × Name) × Nat :=
  let action : DecodeM (Expr × Name) := do
    let value ← decode env realization
    let view ← spine value
    return (value, view.head.constName?.getD realization)
  let (result, state) := action.run.run { fuel, cap := fuel + 1 }
  (result, state.spent)

-- Only the declared carrier selectors may enter the record decoder from type
-- classification. Arbitrary data expressions have no such reduction boundary.
def carrier (env : Environment) (e : Expr) (fuel : Nat) : Option Expr × Nat :=
  let action : DecodeM Expr := recordHead env depthLimit e
  let (result, state) := action.run.run { fuel, cap := fuel + 1 }
  (result, state.spent)

end LeanInformationAudit.RegistrationGates.ReadoutFamily

