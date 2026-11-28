module
public import Init.Grind.FieldNormNum
import Init.GrindInstances
public import Lean
import all Lean.Util.CollectAxioms

/-!
Rational inversion in a quotient of the integers modulo eight. For a proposition `P`,
two residues represent the same element when they coincide, or when `P` holds and
their parities coincide. Under `¬¬ P`, a nonzero class must have odd parity. Odd
residues are their own multiplicative inverses. On even residues the inverse swaps
two and four and fixes zero and six.

The reductions use propositional extensionality and quotient soundness. Division
and integer powers expose the rational operation and the single value it must take
so that the reduction itself does not import the choice dependencies of those
official operations.
-/

open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
namespace OmegaChecks.InitBoundaries.FieldNormalization

private abbrev R := Fin 8
private def parity (x : R) := x.val % 2

private def rel (P : Prop) (x y : R) := x = y ∨ P ∧ parity x = parity y

private def residueSetoid (P : Prop) : Setoid R where
  r := rel P
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun e => Or.inl e.symm) (fun ⟨p, e⟩ => Or.inr ⟨p, e.symm⟩)
    trans := fun h k => h.elim (fun e => e ▸ k) fun ⟨p, e⟩ =>
      k.elim (fun e' => e' ▸ Or.inr ⟨p, e⟩) fun ⟨_, e'⟩ => Or.inr ⟨p, e.trans e'⟩ }

private abbrev Q (P : Prop) := Quotient (residueSetoid P)
private def mk (P : Prop) (x : R) : Q P := Quotient.mk _ x

private def liftUnary (P : Prop) (f : R → R)
    (h : ∀ x y, parity x = parity y → parity (f x) = parity (f y)) (a : Q P) : Q P :=
  Quotient.liftOn a (fun x => mk P (f x)) fun x y eq =>
    Quotient.sound (s := residueSetoid P) (eq.elim (fun e => Or.inl (congrArg f e)) fun ⟨p, e⟩ => Or.inr ⟨p, h x y e⟩)

private def liftBinary (P : Prop) (f : R → R → R)
    (h : ∀ x y, parity x = parity y → ∀ t, parity (f x t) = parity (f y t))
    (k : ∀ x y, parity x = parity y → ∀ t, parity (f t x) = parity (f t y)) (a b : Q P) : Q P :=
  Quotient.liftOn₂ a b (fun x y => mk P (f x y)) fun _ _ _ _ l r => Quotient.sound (s := residueSetoid P) <|
    (residueSetoid P).iseqv.trans (l.elim (fun e => Or.inl (congrArg (f · _) e)) fun ⟨p, e⟩ => Or.inr ⟨p, h _ _ e _⟩)
      (r.elim (fun e => Or.inl (congrArg (f _ ·) e)) fun ⟨p, e⟩ => Or.inr ⟨p, k _ _ e _⟩)

private def addQ (P : Prop) := liftBinary P (· + ·) (by decide) (by decide)
private def mulQ (P : Prop) := liftBinary P (· * ·) (by decide) (by decide)
private def negQ (P : Prop) := liftUnary P (- ·) (by decide)

private def valInv (x : R) : R := if x = 2 then 4 else if x = 4 then 2 else x
private def invQ (P : Prop) := liftUnary P valInv (by decide)

private def powQ (P : Prop) (x : Q P) : Nat → Q P
  | 0 => mk P 1
  | n + 1 => mulQ P (powQ P x n) x

private instance ringQ (P : Prop) : CommRing (Q P) where
  add := addQ P
  mul := mulQ P
  neg := negQ P
  sub a b := addQ P a (negQ P b)
  npow := ⟨powQ P⟩
  ofNat n := ⟨mk P (OfNat.ofNat n)⟩
  natCast := ⟨fun n => mk P (n : R)⟩
  intCast := ⟨fun i => mk P (i : R)⟩
  nsmul := ⟨fun n x => mulQ P (mk P (n : R)) x⟩
  zsmul := ⟨fun i x => mulQ P (mk P (i : R)) x⟩
  add_zero a := Quotient.inductionOn a fun _ => congrArg (mk P) (Semiring.add_zero _)
  add_comm a b := Quotient.inductionOn₂ a b fun _ _ => congrArg (mk P) (Semiring.add_comm _ _)
  add_assoc a b c := Quotient.inductionOn₃ a b c fun _ _ _ => congrArg (mk P) (Semiring.add_assoc _ _ _)
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun _ _ _ => congrArg (mk P) (Semiring.mul_assoc _ _ _)
  mul_comm a b := Quotient.inductionOn₂ a b fun _ _ => congrArg (mk P) (CommSemiring.mul_comm _ _)
  mul_one a := Quotient.inductionOn a fun _ => congrArg (mk P) (Semiring.mul_one _)
  one_mul a := Quotient.inductionOn a fun _ => congrArg (mk P) (Semiring.one_mul _)
  mul_zero a := Quotient.inductionOn a fun _ => congrArg (mk P) (Semiring.mul_zero _)
  right_distrib a b c := Quotient.inductionOn₃ a b c fun _ _ _ => congrArg (mk P) (Semiring.right_distrib _ _ _)
  left_distrib a b c := Quotient.inductionOn₃ a b c fun _ _ _ => congrArg (mk P) (Semiring.left_distrib _ _ _)
  zero_mul a := Quotient.inductionOn a fun _ => congrArg (mk P) (Semiring.zero_mul _)
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  neg_add_cancel a := Quotient.inductionOn a fun _ => congrArg (mk P) (Ring.neg_add_cancel _)
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i a := Quotient.inductionOn a fun x =>
    congrArg (mk P) (show (((-i : Int) : R) * x) = -((i : R) * x) by
      rw [Ring.intCast_neg, Ring.neg_mul])
  ofNat_succ n := congrArg (mk P) (Semiring.ofNat_succ (α := R) n)
  intCast_neg i := congrArg (mk P) (Ring.intCast_neg (α := R) i)


private def ipow (P : Prop) (a : Q P) : Int → Q P
  | .ofNat n => powQ P a n
  | .negSucc n => invQ P (powQ P a (n + 1))

private theorem invInv (P : Prop) (a : Q P) : invQ P (invQ P a) = a :=
  Quotient.inductionOn a fun i => congrArg (mk P) ((by decide : ∀ x : R, valInv (valInv x) = x) i)

@[instance_reducible] private def quotientField (P : Prop) (nn : ¬¬ P) : Field (Q P) where
  toCommRing := ringQ P
  inv := invQ P
  div a b := mulQ P a (invQ P b)
  div_eq_mul_inv _ _ := rfl
  zpow := ⟨ipow P⟩
  zero_ne_one e := by
    have he : rel P 0 1 := Quotient.exact (s := residueSetoid P) e
    exact he.elim (by decide : (0 : R) ≠ 1) (fun h => (by decide : parity 0 ≠ parity 1) h.2)
  inv_zero := rfl
  mul_inv_cancel := by
    intro a
    refine Quotient.inductionOn a ?_
    intro v nz
    by_cases h : parity v = 0
    · exact False.elim (nn (fun p => nz (Quotient.sound (s := residueSetoid P) (Or.inr ⟨p, h⟩))))
    · exact congrArg (mk P) ((by decide : ∀ i : R, parity i ≠ 0 → i * valInv i = 1) v h)
  zpow_zero _ := rfl
  zpow_succ _ _ := rfl
  zpow_neg a z := by
    cases z with
    | ofNat n => cases n <;> rfl
    | negSucc n => exact (invInv P (powQ P a (n + 1))).symm

@[expose] public def twoThirds : Rat := ⟨2, 3, by decide, by decide⟩
@[expose] public def threeHalves : Rat := ⟨3, 2, by decide, by decide⟩

private theorem propositionOfEquality (P : Prop) {i j : R} (ne : i ≠ j) (e : mk P i = mk P j) : P := by
  have rel : rel P i j := Quotient.exact (s := residueSetoid P) e
  exact rel.elim (fun eq => False.elim (ne eq)) And.left

private theorem castNotZero (P : Prop) (i : R) (odd : parity i ≠ 0) (e : mk P i = mk P 0) : False := by
  have eq : rel P i 0 := Quotient.exact (s := residueSetoid P) e
  exact eq.elim (fun h => odd (congrArg parity h)) (fun h => odd h.2)

/-- The inverse split itself is constructive for every supplied zero decision. -/
public theorem inverseSplitWithDecision {α : Type u} [Field α] (a : α) (d : Decidable (a = 0)) :
    @ite Prop (a = 0) d (a⁻¹ = 0) (a * a⁻¹ = 1) := by
  cases d with
  | isTrue h => cases h; exact Field.inv_zero
  | isFalse h => exact Field.mul_inv_cancel h

/-- A decision for the zero test occurring in every pinned inverse split decides
equality of any two elements by applying it to their difference. -/
public def fieldEquality (zero : ∀ {α : Type u} [Field α] (a : α), Decidable (a = 0))
    {α : Type u} [Field α] (a b : α) : Decidable (a = b) :=
  match zero (a - b) with
  | .isTrue h => .isTrue ((AddCommGroup.sub_eq_iff.mp h).trans (AddCommMonoid.zero_add b))
  | .isFalse h => .isFalse (fun eq => h (eq ▸ AddCommGroup.sub_self a))

open scoped Classical in
example : type_of% @CommRing.inv_split.{u} := fun {_} _ a =>
  inverseSplitWithDecision a (Classical.propDecidable _)

/-- In the residue field, two is zero exactly when the proposition identifies
the even residues. A zero decision therefore eliminates double negation. -/
public theorem eliminateDoubleNegationFromFieldZero
    (zero : ∀ {α : Type} [Field α] (a : α), Decidable (a = 0)) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  cases zero (mk P 2) with
  | isTrue h => exact propositionOfEquality P (i := 2) (j := 0) (by decide) h
  | isFalse h => exact False.elim (nn (fun p => h (Quotient.sound (s := residueSetoid P) (Or.inr ⟨p, rfl⟩))))

/-- The even residues expose product, power, and division laws that distinguish the quotient
before its parity classes are identified. -/
public theorem inverseProduct (rule : type_of% @Field.inv_mul.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  exact propositionOfEquality P (i := 2) (j := 0) (by decide) (rule (mk P 2) (mk P 2))

public theorem inverseNegative (rule : type_of% @Field.inv_neg.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  exact propositionOfEquality P (i := 6) (j := 4) (by decide) (rule (mk P 2))

public theorem productZero (rule : type_of% @Field.of_mul_eq_zero.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  cases rule (a := mk P 2) (b := mk P 4) rfl with
  | inl h => exact propositionOfEquality P (i := 2) (j := 0) (by decide) h
  | inr h => exact propositionOfEquality P (i := 4) (j := 0) (by decide) h

public theorem powerZero (rule : type_of% @Field.of_pow_eq_zero.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  exact propositionOfEquality P (i := 2) (j := 0) (by decide) (rule (mk P 2) 3 rfl)

public theorem divideLeft (rule : type_of% @Field.div_div_left.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  exact propositionOfEquality P (i := 0) (j := 2) (by decide)
    (rule (x := mk P 1) (y := mk P 2) (z := mk P 2))

public theorem divideRight (rule : type_of% @Field.div_div_right.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  exact propositionOfEquality P (i := 2) (j := 0) (by decide)
    (rule (x := mk P 1) (y := mk P 2) (z := mk P 4))

open Lean.Grind.Field.NormNum

private theorem inverseR : twoThirds⁻¹ = threeHalves := by decide +kernel
public theorem dividedR : 1 / threeHalves = twoThirds := by decide +kernel
public theorem poweredR : twoThirds ^ (-1 : Int) = threeHalves := by decide +kernel

public theorem inverse (rule : type_of% @ofRat_inv.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  have h := rule (α := Q P) twoThirds
  rw [inverseR] at h
  exact propositionOfEquality P (i := 4) (j := 6) (by decide) h

public theorem verifyInv (rule : type_of% @inv_eq.{0}) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  apply propositionOfEquality P (i := 4) (j := 6) (by decide)
  exact (rule (ofRat twoThirds : Q P) twoThirds threeHalves (by rw [inverseR]; decide +kernel) rfl).symm
/-- Division with its rational operator as an explicit argument. -/
@[expose] public def DivideLaw (divide : Rat → Rat → Rat) : Prop :=
  ∀ {α : Type} [Field α] {a b : Rat}, (a.den : α) ≠ 0 → (b.num : α) ≠ 0 →
    (ofRat (divide a b) : α) = ofRat a / ofRat b

/-- Integer powers with their rational operator as an explicit argument. -/
@[expose] public def PowerLaw (power : Rat → Int → Rat) : Prop :=
  ∀ {α : Type} [Field α] {a : Rat}, (a.den : α) ≠ 0 → ∀ n : Int,
    (ofRat (power a n) : α) = ofRat a ^ n

public theorem pinnedDivisionType : DivideLaw (· / ·) = (type_of% @ofRat_div'.{0}) := rfl
public theorem pinnedPowerType : PowerLaw (· ^ ·) = (type_of% @ofRat_zpow'.{0}) := rfl

public theorem divide (op : Rat → Rat → Rat) (compute : op 1 threeHalves = twoThirds)
    (rule : DivideLaw op) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  have h := rule (α := Q P) (a := 1) (b := threeHalves)
    (castNotZero P 1 (by decide)) (castNotZero P 3 (by decide))
  rw [compute] at h
  exact propositionOfEquality P (i := 2) (j := 6) (by decide) h.symm

public theorem power (op : Rat → Int → Rat) (compute : op twoThirds (-1) = threeHalves)
    (rule : PowerLaw op) (P : Prop) (nn : ¬¬ P) : P := by
  letI := quotientField P nn
  have h := rule (α := Q P) (a := twoThirds) (castNotZero P 3 (by decide)) (-1)
  rw [compute] at h
  exact propositionOfEquality P (i := 4) (j := 6) (by decide) h


run_cmd
  for witness in #[``inverseSplitWithDecision, ``fieldEquality] do
    unless (← Lean.collectAxioms witness).isEmpty do
      throwError "the supplied field decision needs extra axioms at {witness}"
  for witness in #[``inverseProduct, ``inverseNegative, ``productZero, ``powerZero, ``divideLeft, ``divideRight,
      ``inverse, ``verifyInv, ``divide, ``power, ``eliminateDoubleNegationFromFieldZero] do
    let axioms ← Lean.collectAxioms witness
    unless axioms.all (#[`propext, `Quot.sound].contains ·) do
      throwError "field normalization reduction {witness} uses extra axioms: {axioms}"

end OmegaChecks.InitBoundaries.FieldNormalization
