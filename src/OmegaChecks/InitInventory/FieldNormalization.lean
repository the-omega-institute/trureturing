module
public import Init.Grind.FieldNormNum
public import OmegaChecks.InitInventory.KripkeModels
import all OmegaChecks.InitInventory.KripkeModels
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

The finite two-world interpretation checks the same residue operations directly.
Its root uses equality modulo eight and its leaf uses equality of parities.
It computes failures of the inverse product, inverse negation, zero product, zero
power and nested division formulas at the root. Each finite-stage witness has an
empty axiom closure.
-/

open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
namespace OmegaChecks.InitBoundaries.FieldNormalization

private abbrev R := Fin 8

@[expose] public def parity (x : Fin 8) := x.val % 2

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

@[expose] public def valInv (x : Fin 8) : Fin 8 :=
  if x.val = 2 then ⟨4, by decide⟩ else if x.val = 4 then ⟨2, by decide⟩ else x
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

open TwoWorlds
namespace FiniteStages
public section

local notation "r0" => (⟨0, by decide⟩ : Fin 8)
local notation "r1" => (⟨1, by decide⟩ : Fin 8)
local notation "r2" => (⟨2, by decide⟩ : Fin 8)
local notation "r4" => (⟨4, by decide⟩ : Fin 8)

/-- At the root values are residues modulo eight. The leaf identifies residues of equal parity. -/
@[expose] def equalAt (x y : Fin 8) : Bool → Prop
  | false => x = y
  | true => parity x = parity y

theorem rootApart (a b : Fin 8) : neg (equalAt a b) false ↔ parity a ≠ parity b := by
  constructor
  · intro h
    exact h true (fun _ => rfl)
  · intro h w _ eq
    cases w with
    | false => exact h (congrArg parity eq)
    | true => exact h eq

theorem persists {w w' : Bool} (h : w ≤ w') (a b : Fin 8) : equalAt a b w → equalAt a b w' := by
  cases w <;> cases w'
  · exact id
  · exact congrArg parity
  · exact False.elim (Bool.noConfusion (h rfl))
  · exact id

/-- Addition, multiplication and negation satisfy the commutative ring equations at the root.
Persistence sends each equation to the leaf. -/
theorem ringLaws :
    (∀ a b c : Fin 8, (a + b) + c = a + (b + c) ∧ (a * b) * c = a * (b * c) ∧
      a * (b + c) = a * b + a * c) ∧
    (∀ a b : Fin 8, a + b = b + a ∧ a * b = b * a) ∧
    (∀ a : Fin 8, a + r0 = a ∧ a * r1 = a ∧ -a + a = r0) := by decide

/-- The projection to parity preserves each nontrivial operation of the residue field. -/
theorem operations :
    (∀ a b c d : Fin 8, parity a = parity b → parity c = parity d →
      parity (a + c) = parity (b + d) ∧ parity (a * c) = parity (b * d)) ∧
    (∀ a b : Fin 8, parity a = parity b → parity (-a) = parity (-b) ∧
      parity (valInv a) = parity (valInv b)) := by decide

/-- The inverse field axiom uses persistent inequality at the current world. -/
theorem cancel : ∀ (a : Fin 8) (w : Bool),
    neg (equalAt a r0) w → equalAt (a * valInv a) r1 w := by
  intro a w h
  cases w with
  | false =>
    exact (by decide : ∀ a : Fin 8, parity a ≠ parity r0 → a * valInv a = r1) a ((rootApart a r0).mp h)
  | true =>
    exact (by decide : ∀ a : Fin 8, parity a ≠ parity r0 → parity (a * valInv a) = parity r1) a
      (h true (fun x => x))

theorem inverseLaws : valInv r0 = r0 ∧
    (∀ a : Fin 8, valInv (valInv a) = a) ∧ neg (equalAt r0 r1) false := by
  exact ⟨rfl, by decide, (rootApart r0 r1).mpr (by decide)⟩

@[expose] def natPower (a : Fin 8) : Nat → Fin 8
  | 0 => r1
  | n + 1 => natPower a n * a

@[expose] def intPower (a : Fin 8) : Int → Fin 8
  | .ofNat n => natPower a n
  | .negSucc n => valInv (natPower a (n + 1))

theorem powerLaws (a : Fin 8) :
    intPower a 0 = r1 ∧ (∀ n : Nat, intPower a (n + 1 : Int) = intPower a (n : Int) * a) ∧
    ∀ n : Int, intPower a (-n) = valInv (intPower a n) := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro n
  cases n with
  | ofNat n => cases n <;> rfl
  | negSucc n => exact (inverseLaws.2.1 _).symm

theorem powerRespectsParity {a b : Fin 8} (h : parity a = parity b) (n : Int) :
    parity (intPower a n) = parity (intPower b n) := by
  have natLaw (k : Nat) : parity (natPower a k) = parity (natPower b k) := by
    induction k with
    | zero => rfl
    | succ _ ih => exact (operations.1 _ _ _ _ ih h).2
  cases n with
  | ofNat n => exact natLaw n
  | negSucc n => exact (operations.2 _ _ (natLaw (n + 1))).2

/-- Root counterexamples to `Field.inv_mul`, `Field.inv_neg` and `Field.of_mul_eq_zero`. -/
theorem counterexamples :
    ¬equalAt (valInv (r2 * r2)) (valInv r2 * valInv r2) false ∧
    ¬equalAt (valInv (-r2)) (-valInv r2) false ∧
    equalAt (r2 * r4) r0 false ∧ ¬(equalAt r2 r0 false ∨ equalAt r4 r0 false) := by
  unfold equalAt
  decide

/-- The interpreted division is multiplication by the interpreted inverse. -/
@[expose] def divideAt (a b : Fin 8) := a * valInv b

/-- Root counterexamples to `Field.of_pow_eq_zero`, `Field.div_div_left` and `Field.div_div_right`. -/
theorem powerAndDivisionCounterexamples :
    equalAt (natPower r2 3) r0 false ∧ ¬equalAt r2 r0 false ∧
    ¬equalAt (divideAt (divideAt r1 r2) r2) (divideAt r1 (r2 * r2)) false ∧
    ¬equalAt (divideAt r1 (divideAt r2 r4)) (divideAt (r1 * r4) r2) false := by
  unfold equalAt
  decide

run_cmd
  for witness in #[``rootApart, ``persists, ``ringLaws, ``operations, ``cancel, ``inverseLaws,
      ``powerLaws, ``powerRespectsParity, ``counterexamples, ``powerAndDivisionCounterexamples] do
    unless (← Lean.collectAxioms witness).isEmpty do
      throwError "finite residue model {witness} uses an axiom"

end
end FiniteStages

end OmegaChecks.InitBoundaries.FieldNormalization
