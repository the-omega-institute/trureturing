module
public import Lean
import OmegaChecks.InitInventory.Replay
import all Init.Grind.Ring.Envelope
import all Init.Grind.Ring.CommSemiringAdapter
import all Init.Grind.Module.Envelope
import Init.GrindInstances.Ring.Nat

namespace OmegaChecks.InitBoundaries.EnvelopeCancellation
open Lean Lean.Grind Std

private abbrev ringPoint := Ring.OfSemiring.Q.mk (α := Nat) (1, 0)
private abbrev modulePoint := IntModule.OfNatModule.Q.mk (α := Nat) (1, 0)

private theorem ringLaw :
    Ring.OfSemiring.add (Ring.OfSemiring.neg ringPoint) ringPoint = Ring.OfSemiring.natCast 0 := Ring.OfSemiring.neg_add_cancel ringPoint
private theorem moduleLaw :
    IntModule.OfNatModule.add (IntModule.OfNatModule.neg modulePoint) modulePoint = IntModule.OfNatModule.zero := IntModule.OfNatModule.neg_add_cancel modulePoint

private theorem ringProjection : type_of% ringLaw :=
  @Ring.neg_add_cancel _ (Ring.OfSemiring.ofSemiring (α := Nat)) ringPoint

private theorem commRingProjection : type_of% ringLaw :=
  @Ring.neg_add_cancel _ (CommRing.OfCommSemiring.ofCommSemiring (α := Nat)).toRing ringPoint

private theorem moduleProjection : type_of% moduleLaw :=
  @AddCommGroup.neg_add_cancel _ (IntModule.OfNatModule.ofNatModule (α := Nat)).toAddCommGroup modulePoint

private abbrev diagonal := IntModule.OfNatModule.Q.mk (α := Nat) (1, 1)
private abbrev zeroPoint := IntModule.OfNatModule.Q.mk (α := Nat) (0, 0)

/-- Both envelope comparisons on these inputs reduce to the reflexive comparison 1 ≤ 1. -/
private theorem partialAntisymmetry : diagonal = zeroPoint :=
  @IsPartialOrder.le_antisymm _ _ (@IntModule.OfNatModule.instIsPartialOrderQ Nat _ _ _ _)
    diagonal zeroPoint (Nat.le_refl 1) (Nat.le_refl 1)

private theorem linearAntisymmetry : diagonal = zeroPoint :=
  @IsPartialOrder.le_antisymm _ _ (@IntModule.OfNatModule.instIsLinearOrderQ Nat _ _ _ _).toIsPartialOrder
    diagonal zeroPoint (Nat.le_refl 1) (Nat.le_refl 1)

private theorem scalarCancellation :
    IntModule.OfNatModule.add (IntModule.OfNatModule.zsmul 1 modulePoint)
      (IntModule.OfNatModule.zsmul (-1) modulePoint) = IntModule.OfNatModule.zsmul (1 + -1) modulePoint :=
  (IntModule.OfNatModule.add_zsmul 1 (-1) modulePoint).symm

private def observations := [
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.neg_add_cancel, ``ringLaw),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.neg_add_cancel, ``moduleLaw),
  (`Init.Grind.Ring.Envelope, ``Ring.OfSemiring.ofSemiring, ``ringProjection),
  (`Init.Grind.Ring.Envelope, ``CommRing.OfCommSemiring.ofCommSemiring, ``commRingProjection),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.ofNatModule, ``moduleProjection),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.add_zsmul, ``scalarCancellation),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.instIsPartialOrderQ, ``partialAntisymmetry),
  (`Init.Grind.Module.Envelope, ``IntModule.OfNatModule.instIsLinearOrderQ, ``linearAntisymmetry)]

public def observation? (owner name : Name) : Option Name := do
  let (_, _, observation) ← observations.find? fun (m, n, _) => m == owner && n == name
  return observation

private def pair (a b : Nat) :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit a) (mkRawNatLit b)

private abbrev natRing : Semiring Nat := inferInstance
private abbrev natModule : NatModule Nat := inferInstance

private theorem relatedAt (n : Nat) : ∃ k : Nat, n + k = n + k := ⟨0, rfl⟩

public def liftOperation? (owner name : Name) : Option Name := do
  let ops ← match owner with
    | `Init.Grind.Ring.Envelope => some [``Ring.OfSemiring.add, ``Ring.OfSemiring.sub,
        ``Ring.OfSemiring.mul, ``Ring.OfSemiring.neg]
    | `Init.Grind.Module.Envelope => some [``IntModule.OfNatModule.add, ``IntModule.OfNatModule.sub,
        ``IntModule.OfNatModule.neg, ``IntModule.OfNatModule.nsmul, ``IntModule.OfNatModule.zsmul]
    | _ => none
  let n := privateToUserName name
  ops.find? fun op => n == op || n == op.str "eq_1"

/-- Check the pinned operation and its unfolding equation at variable quotient arguments.
The bare operation signatures also admit constant functions. The coherence proof for the
specified representative computation must identify the classes of (1,1) and (0,0). -/
private def liftEquationClaim (official witnesses : Environment) (owner op : Name)
    (source : ConstantInfo) : IO Expr := do
  let ring := owner == `Init.Grind.Ring.Envelope
  let fixture := if ring then ``natRing else ``natModule
  let some inst := (witnesses.find? fixture).bind ConstantInfo.value? | throw <| IO.userError s!"missing {fixture}"
  let some (.defnInfo impl) := official.find? op | throw <| IO.userError s!"missing pinned operation {op}"
  let equationName := if ring then op.str "eq_1" else mkPrivateNameCore owner (op.str "eq_1")
  let some (.thmInfo equation) := official.find? equationName | throw <| IO.userError s!"missing {equationName}"
  unless source.name == op || source.name == equationName do throw <| IO.userError s!"wrong site {source.name}"
  -- At scalar one both lifted actions return the class of the input representative.
  let scalar := if op == ``IntModule.OfNatModule.nsmul then #[mkRawNatLit 1]
    else if op == ``IntModule.OfNatModule.zsmul then #[mkApp (mkConst ``Int.ofNat) (mkRawNatLit 1)]
    else #[]
  let params := #[mkConst ``Nat, inst] ++ scalar
  let unary := !scalar.isEmpty || op.getString! == "neg"
  let lift := if unary then ``Quot.liftOn else if ring then ``Ring.OfSemiring.Q.liftOn₂ else ``IntModule.OfNatModule.Q.liftOn₂
  -- Multiplication fixes (1,0), its unit representative. Addition and subtraction fix (0,0).
  let fixed := if op == ``Ring.OfSemiring.mul then 1 else 0
  let evidence (n : Nat) := mkApp (mkConst ``relatedAt) (mkRawNatLit n)
  let args := if unary then #[pair 1 1, pair 0 0, evidence 1]
    else #[pair 1 1, pair fixed 0, pair 0 0, pair fixed 0, evidence 1, evidence fixed]
  let clean ← replayBoundaryDependencies official witnesses (args.toList.flatMap (·.getUsedConstantsAsSet.toList))
  for arg in args do
    if let .error _ := Kernel.check clean {} arg then throw <| IO.userError "invalid coherence test input"
  let test := do
    let equationType := equation.type.instantiateLevelParams equation.levelParams [0]
    let rest := params.foldl (fun (t : Expr) arg => t.bindingBody!.instantiate1 arg) equationType
    Meta.forallTelescope rest fun qs conclusion => do
      let some (_, lhs, rhs) := conclusion.eq? | throwError "expected an unfolding equality"
      unless qs.size == (if unary then 1 else 2) && lhs == mkAppN (mkConst op [0]) (params ++ qs) &&
          rhs.getAppFn.isConstOf lift do
        throwError "unexpected unfolding equation for {source.name}"
      let body := (impl.value.instantiateLevelParams impl.levelParams [0]).beta (params ++ qs)
      unless body.getAppFn.isConstOf lift && Kernel.isDefEqGuarded official (← getLCtx) body rhs do
        throwError "pinned body and unfolding equation disagree for {op}"
      let .forallE _ required _ _ ← Meta.whnf (← Meta.inferType rhs.appFn!) | throwError "missing coherence argument"
      let ctx ← getLCtx
      unless Kernel.isDefEqGuarded witnesses ctx (← Meta.inferType rhs.appArg!) required && !required.hasFVar do
        throwError "unexpected coherence type for {source.name}"
      Meta.withLocalDeclD `respect required fun respect => do
        let claim ← ofExceptKernelException (Kernel.check witnesses (← getLCtx) (mkAppN respect args))
        unless !claim.hasFVar do throwError "coherence result depends on the supplied proof"
        return claim
  (Meta.MetaM.run' test).toIO' {fileName := "<envelope lift coherence>", fileMap := default} {env := witnesses}

/-- Obtain an equality by applying the physical declaration or its cancellation field.
Reduce both sides to the pinned quotient constructor and check its relation and payload.
The returned equality is the observation in the representative model. -/
public def counterexample (official witnesses : Environment) (source : ConstantInfo) (modelPoint : Name) : IO Expr := do
  let some idx := official.getModuleIdxFor? source.name | throw <| IO.userError s!"missing owner for {source.name}"
  let owner := official.header.moduleNames[idx]!
  let claim ← if let some op := liftOperation? owner source.name then liftEquationClaim official witnesses owner op source else do
    let some probe := observation? owner source.name
      | throw <| IO.userError s!"unexpected envelope declaration {source.name}"
    let some (.thmInfo template) := witnesses.find? probe | throw <| IO.userError s!"missing {probe}"
    let call := template.value.replace fun e =>
      if [``ringPoint, ``modulePoint, ``diagonal, ``zeroPoint].any e.isConstOf then
        (witnesses.find? e.constName!).bind ConstantInfo.value?
      else none
    unless call.getUsedConstantsAsSet.contains source.name && (official.find? source.name).any (·.type.equal source.type) do
      throw <| IO.userError s!"probe does not use the declared envelope {source.name}"
    IO.ofExcept <| (Kernel.check official {} call).mapError fun _ => s!"failed to specialize {source.name}"
  let .ok claim := Kernel.whnf official {} claim | throw <| IO.userError s!"invalid cancellation type for {source.name}"
  let some (_, lhs, rhs) := claim.eq? | throw <| IO.userError s!"expected cancellation equality for {source.name}"
  let reduce (side : Expr) (value : Nat) := do
    let .ok root := Kernel.whnf official {} side | throw <| IO.userError s!"failed to reduce {source.name}"
    unless root.isAppOfArity ``Quot.mk 3 && Kernel.isDefEqGuarded official {} root.appArg! (pair value value) do
      throw <| IO.userError s!"unexpected cancellation endpoint for {source.name}"
    return root.appFn!
  let leftPoint ← reduce lhs 1
  let rightPoint ← reduce rhs 0
  unless Kernel.isDefEqGuarded official {} leftPoint rightPoint do
    throw <| IO.userError s!"cancellation endpoints of {source.name} use different quotient relations"
  let carrier := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
  let relation := Expr.forallE `x carrier (.forallE `y carrier (.sort .zero) .default) .default
  let point := mkApp2 (mkConst modelPoint [1]) carrier (.bvar 0)
  let equality := mkApp3 (mkConst ``Eq [1]) carrier (mkApp point (pair 1 1)) (mkApp point (pair 0 0))
  return .forallE `r relation (.forallE `h equality (mkConst ``False) .default) .default

end OmegaChecks.InitBoundaries.EnvelopeCancellation

open Lean.Grind Ring.OfSemiring
namespace OmegaChecks.InitBoundaries.RingEnvelopeExact

/- The upstream Q.exact descends a proposition-valued relation via propositional
extensionality. The upstream toQ_inj applies exactness to (a, 0) and (b, 0).
The proofs below construct these conclusions when a row of the relation is
decidable or there is a separating additive map. The unrestricted types of
Q.exact and toQ_inj remain open. -/

variable {α : Type u} [Semiring α]

private def observe (p : α × α) [∀ x, Decidable (r α p x)] : Q α → Bool :=
  Quot.lift (fun x => decide (r α p x)) fun _ _ h =>
    decide_eq_decide.mpr ⟨fun hx => r_trans hx h, fun hy => r_trans hy (r_sym h)⟩

public theorem exactOfDecidable {p q : α × α} [∀ x, Decidable (r α p x)]
    (eq : Q.mk p = Q.mk q) : r α p q :=
  of_decide_eq_true ((congrArg (observe p) eq).symm.trans (decide_eq_true (r_rfl p)))

public theorem cancellativeRelation [AddRightCancel α] (p q : α × α) :
    r α p q ↔ p.1 + q.2 = p.2 + q.1 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  constructor
  · rintro ⟨k, h⟩
    exact AddRightCancel.add_right_cancel _ _ k h
  · intro h
    exact ⟨0, congrArg (· + 0) h⟩

public theorem embeddingOfDecidableEq [AddRightCancel α] [DecidableEq α] {a b : α}
    (eq : toQ a = toQ b) : a = b := by
  let p : α × α := (a, 0)
  let q : α × α := (b, 0)
  letI (x : α × α) : Decidable (r α p x) :=
    decidable_of_iff' (p.1 + x.2 = p.2 + x.1) (cancellativeRelation p x)
  have h := (cancellativeRelation p q).mp (exactOfDecidable (p := p) (q := q) eq)
  exact (Semiring.add_zero a).symm.trans (h.trans (AddCommMonoid.zero_add b))

section
variable {G : Type v} [AddCommGroup G] (f : α → G)
variable (add : ∀ a b, f (a + b) = f a + f b)

private theorem regroup (a b d : G) :
    (a - b) + (b + d) = a + d := by
  rw [← AddCommMonoid.add_assoc, AddCommGroup.sub_add_cancel]

private theorem crossEq (a b c d : G) :
    a - b = c - d ↔ a + d = b + c := by
  have cancel := @AddCommGroup.add_left_inj G _ (a - b) (c - d) (b + d)
  rw [regroup, AddCommMonoid.add_comm b d, regroup, AddCommMonoid.add_comm c b] at cancel
  exact cancel.symm

private def difference : Q α → G :=
  Quot.lift (fun x : α × α => f x.1 - f x.2) fun ⟨a, b⟩ ⟨c, d⟩ ⟨k, h⟩ => by
    apply (crossEq _ _ _ _).mpr
    have e := congrArg f h
    change f (a + d + k) = f (b + c + k) at e
    simp only [add] at e
    exact (AddCommGroup.add_left_inj (f k)).mp e

include add

/-- Mapping each pair to its difference in an additive commutative group reflects
the envelope relation when the original additive map is injective. -/
public theorem exactOfAdditiveEmbedding (inj : ∀ {a b}, f a = f b → a = b)
    {p q : α × α} (e : Q.mk p = Q.mk q) : r α p q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  have eq := congrArg (difference f add) e
  change f a - f b = f c - f d at eq
  replace eq := (crossEq _ _ _ _).mp eq
  have h : a + d = b + c := inj (((add _ _).trans eq).trans (add _ _).symm)
  exact ⟨0, congrArg (· + 0) h⟩

/-- The zero-class embedding reflects equality under the same hypothesis,
without a cancellation or decidability instance on the source. -/
public theorem embeddingOfAdditiveEmbedding (inj : ∀ {a b}, f a = f b → a = b)
    {a b : α} (e : toQ a = toQ b) : a = b := by
  have eq := congrArg (difference f add) e
  change f a - f 0 = f b - f 0 at eq
  replace eq := (crossEq _ _ _ _).mp eq
  rw [AddCommMonoid.add_comm (f 0) (f b)] at eq
  exact inj ((AddCommGroup.add_left_inj (f 0)).mp eq)

end

open Lean.Grind.CommRing

public abbrev ReflectsDisequality : Prop :=
  ∀ {α : Type u} [Semiring α] [AddRightCancel α] {a b : α}, a ≠ b → toQ a ≠ toQ b

/-- Two leaves recover arbitrary semiring elements from variable expressions.
The converse transports both sides of the interpreter agreement. -/
public theorem adapterIff :
    (type_of% @Ring.OfSemiring.of_diseq.{u}) ↔ ReflectsDisequality.{u} := by
  constructor
  · intro law α _ _ a b h
    exact law (.branch 1 (.leaf a) (.leaf b)) (.var 0) (.var 1) h
  · intro reflect α _ _ ctx lhs rhs h e
    apply reflect h
    exact (Expr.denoteAsRing_eq ctx lhs).symm.trans (e.trans (Expr.denoteAsRing_eq ctx rhs))

end OmegaChecks.InitBoundaries.RingEnvelopeExact
