module
public import Lean
import Lean.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.Logic

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

namespace WeakRingOrder

open Lean.Grind Std

def PositiveMultipliers : Prop := ∀ {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] {a b c : R}, 0 < c → a ≤ b → a*c ≤ b*c

theorem fromPosRight (f : type_of% @Field.IsOrdered.mul_le_mul_iff_of_pos_right.{u}) :
    PositiveMultipliers.{u} := fun {_} _ _ _ _ _ _ {_ _ _} h => (f h).mpr

theorem fromPosLeft (f : type_of% @Field.IsOrdered.mul_le_mul_iff_of_pos_left.{u}) :
    PositiveMultipliers.{u} := by
  intro R _ _ _ _ _ _ a b c pos le
  rw [CommSemiring.mul_comm a, CommSemiring.mul_comm b]
  exact (f pos).mpr le

theorem fromDivision (f : type_of% @Field.IsOrdered.le_mul_inv_iff_mul_le.{u}) :
    PositiveMultipliers.{u} := by
  intro R _ _ _ _ _ _ a b c pos le
  apply (f a (b*c) pos).mp
  have nz : c ≠ 0 := fun eq =>
    ((Std.LawfulOrderLT.lt_iff _ _).mp pos).2 (eq ▸ Std.IsPreorder.le_refl _)
  rwa [Semiring.mul_assoc, Field.mul_inv_cancel nz, Semiring.mul_one]

def NonnegativeProducts : Prop := ∀ {R : Type u} [Ring R] [LE R] [LT R] [IsPartialOrder R]
  [OrderedRing R] [LawfulOrderLT R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a*b

theorem fromLeft (f : type_of% @OrderedRing.mul_le_mul_of_nonneg_left.{u}) : NonnegativeProducts.{u} := by
  intro R _ _ _ _ _ _ a b ha hb
  have prod := f hb ha
  rwa [Semiring.mul_zero] at prod

theorem fromRight (f : type_of% @OrderedRing.mul_le_mul_of_nonneg_right.{u}) : NonnegativeProducts.{u} := by
  intro R _ _ _ _ _ _ a b ha hb
  have prod := f ha hb
  rwa [Semiring.zero_mul] at prod

private theorem toNegative {R : Type u} [Ring R] [LE R] [LT R] [IsPartialOrder R] [OrderedRing R]
    {a : R} (h : 0 ≤ a) : -a ≤ 0 := by
  have shift := (OrderedAdd.add_le_left_iff (-a)).mp h
  rwa [AddCommMonoid.zero_add, AddCommGroup.add_neg_cancel] at shift

private theorem eqOfRightSums {R : Type u} [Ring R] {a b t : R} (h : a+t = b+t) : a = b := by
  have eq := congrArg (· + -t) h
  rwa [AddCommMonoid.add_assoc, AddCommMonoid.add_assoc, AddCommGroup.add_neg_cancel,
    AddCommMonoid.add_zero, AddCommMonoid.add_zero] at eq

private theorem doubleNegativeProduct {R : Type u} [Ring R] (a b : R) : (-a)*(-b) = a*b := by
  apply eqOfRightSums (t := (-a)*b)
  rw [← Semiring.left_distrib, AddCommGroup.neg_add_cancel, Semiring.mul_zero,
    ← Semiring.right_distrib, AddCommGroup.add_neg_cancel, Semiring.zero_mul]

theorem fromLeftNeg (f : type_of% @OrderedRing.mul_le_mul_of_nonpos_left.{u}) : NonnegativeProducts.{u} := by
  intro R _ _ _ _ _ _ a b ha hb
  have prod := f (toNegative hb) (toNegative ha)
  rwa [Semiring.mul_zero, doubleNegativeProduct] at prod

theorem fromRightNeg (f : type_of% @OrderedRing.mul_le_mul_of_nonpos_right.{u}) : NonnegativeProducts.{u} := by
  intro R _ _ _ _ _ _ a b ha hb
  have prod := f (toNegative ha) (toNegative hb)
  rwa [Semiring.zero_mul, doubleNegativeProduct] at prod

theorem fromTwoNonpositive (f : type_of% @OrderedRing.mul_nonneg_of_nonpos_of_nonpos.{u}) :
    NonnegativeProducts.{u} := by
  intro R _ _ _ _ _ _ a b ha hb
  have prod := f (toNegative ha) (toNegative hb)
  rwa [doubleNegativeProduct] at prod

private theorem negateLE {R : Type u} [Ring R] [LE R] [LT R] [IsPartialOrder R] [OrderedRing R]
    {a b : R} (le : a ≤ b) : -b ≤ -a := by
  apply (OrderedAdd.add_le_left_iff b).mpr
  rw [AddCommGroup.neg_add_cancel]
  apply (OrderedAdd.add_le_left_iff a).mpr
  rw [AddCommMonoid.zero_add, AddCommMonoid.add_comm (-a) b, AddCommMonoid.add_assoc,
    AddCommGroup.neg_add_cancel, AddCommMonoid.add_zero]
  exact le

private theorem doubleNeg {R : Type u} [Ring R] (a : R) : -(-a) = a := by
  apply eqOfRightSums (t := -a)
  rw [AddCommGroup.neg_add_cancel, AddCommGroup.add_neg_cancel]

private theorem positiveNeg {R : Type u} [Ring R] [LE R] [LT R] [IsPartialOrder R]
    [OrderedRing R] [LawfulOrderLT R] {a : R} (h : 0 < a) : -a < 0 := by
  obtain ⟨ha, na⟩ := (LawfulOrderLT.lt_iff _ _).mp h
  refine (LawfulOrderLT.lt_iff _ _).mpr ⟨toNegative ha, fun contra => na ?_⟩
  have shift := (OrderedAdd.add_le_left_iff a).mp contra
  rwa [AddCommMonoid.zero_add, AddCommGroup.neg_add_cancel] at shift

private theorem mulNegative {R : Type u} [Ring R] (a b : R) : a * (-b) = -(a*b) := by
  apply eqOfRightSums (t := a*b)
  rw [← Semiring.left_distrib, AddCommGroup.neg_add_cancel, Semiring.mul_zero, AddCommGroup.neg_add_cancel]

private theorem nonnegOfNegLE {R : Type u} [Ring R] [LE R] [LT R] [IsPartialOrder R] [OrderedRing R]
    {r : R} (le : -r ≤ 0) : 0 ≤ r := by
  have eq := (OrderedAdd.add_le_left_iff r).mp le
  rwa [AddCommGroup.neg_add_cancel, AddCommMonoid.zero_add] at eq

theorem fromNegRight (f : type_of% @Field.IsOrdered.mul_le_mul_iff_of_neg_right.{u}) :
    PositiveMultipliers.{u} := by
  intro R _ _ _ _ _ _ a b c pos le
  have h := (f (positiveNeg pos)).mpr le
  rw [mulNegative, mulNegative] at h
  have h' := negateLE h
  rwa [doubleNeg, doubleNeg] at h'

theorem fromNegLeft (f : type_of% @Field.IsOrdered.mul_le_mul_iff_of_neg_left.{u}) :
    PositiveMultipliers.{u} := by
  intro R _ _ _ _ _ _ a b c pos le
  have h := (f (positiveNeg pos)).mpr le
  rw [CommSemiring.mul_comm (-c) b, CommSemiring.mul_comm (-c) a, mulNegative, mulNegative] at h
  have h' := negateLE h
  rwa [doubleNeg, doubleNeg] at h'

theorem fromMixedRight (f : type_of% @OrderedRing.mul_nonpos_of_nonneg_of_nonpos.{u}) :
    NonnegativeProducts.{u} := by
  intro R _ _ _ _ _ _ a b ha hb
  have h := f ha (toNegative hb)
  rw [mulNegative] at h
  exact nonnegOfNegLE h

theorem fromMixedLeft (f : type_of% @OrderedRing.mul_nonpos_of_nonpos_of_nonneg.{u}) :
    NonnegativeProducts.{u} := by
  intro R _ _ _ _ _ _ a b ha hb
  have h := f (toNegative ha) hb
  have opposite : (-a)*b = -(a*b) := by
    apply eqOfRightSums (t := a*b)
    rw [← Semiring.right_distrib, AddCommGroup.neg_add_cancel, Semiring.zero_mul, AddCommGroup.neg_add_cancel]
  exact nonnegOfNegLE (opposite ▸ h)

private theorem negativeNonzero {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
    [IsLinearOrder R] [OrderedRing R] {c : R} (neg : c < 0) : c ≠ 0 := by
  rintro rfl
  exact ((Std.LawfulOrderLT.lt_iff _ _).mp neg).2 (Std.IsPreorder.le_refl _)

theorem fromNegativeDivision (f : type_of% @Field.IsOrdered.le_mul_inv_iff_le_mul_of_neg.{u}) :
    PositiveMultipliers.{u} := by
  intro R _ _ _ _ _ _ a b c pos le
  have neg := positiveNeg pos
  have h := (f a (b*(-c)) neg).mp (by
    rwa [Semiring.mul_assoc, Field.mul_inv_cancel (negativeNonzero neg), Semiring.mul_one])
  rw [mulNegative, mulNegative] at h
  have h' := negateLE h
  rwa [doubleNeg, doubleNeg] at h'

theorem fromNegativeDivisionLeft (f : type_of% @Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg.{u}) :
    PositiveMultipliers.{u} := by
  intro R _ _ _ _ _ _ a b c pos le
  have neg := positiveNeg pos
  have h := (f (a*(-c)) b neg).mp (by
    rwa [Semiring.mul_assoc, Field.mul_inv_cancel (negativeNonzero neg), Semiring.mul_one])
  rw [mulNegative, mulNegative] at h
  have h' := negateLE h
  rwa [doubleNeg, doubleNeg] at h'

/-- Opposite weak signs of a nonnegative element and its reciprocal force the reciprocal to vanish. -/
def OppositeSigns : Prop := ∀ {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] {a : R}, 0 ≤ a → a⁻¹ ≤ 0 → a⁻¹ = 0

theorem fromInverseNonneg (f : type_of% @Field.IsOrdered.inv_nonneg_iff.{u}) :
    OppositeSigns.{u} := fun {_} _ _ _ _ _ _ {_} ha h => IsPartialOrder.le_antisymm _ _ h (f.mpr ha)

theorem fromInverseNonpos (f : type_of% @Field.IsOrdered.inv_nonpos_iff.{u}) :
    OppositeSigns.{u} := by
  intro R _ _ _ _ _ _ a ha hi
  have zero : a = 0 := IsPartialOrder.le_antisymm _ _ (f.mp hi) ha
  rw [zero, Field.inv_zero]

/-- Squares of elements with a chosen weak sign are nonnegative even in a partial order. -/
def SignedSquare : Prop := ∀ {R : Type u} [Ring R] [LE R] [LT R] [IsPartialOrder R]
  [OrderedRing R] [LawfulOrderLT R] {a : R}, (0 ≤ a ∨ a ≤ 0) → 0 ≤ a*a

theorem signedSquareOfProduct (f : type_of% @OrderedRing.mul_nonneg.{u}) : SignedSquare.{u} := by
  intro R _ _ _ _ _ _ a sign
  cases sign with
  | inl ha => exact f ha ha
  | inr ha =>
    have h := (OrderedAdd.add_le_left_iff (-a)).mp ha
    rw [AddCommGroup.add_neg_cancel, AddCommMonoid.zero_add] at h
    have pos := f h h
    rwa [doubleNegativeProduct] at pos

def LinearSquare : Prop := ∀ {R : Type u} [Ring R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] (a : R), 0 ≤ a*a

theorem squareOfProductSigns (f : type_of% @OrderedRing.mul_nonneg_iff.{u}) : LinearSquare.{u} := by
  intro R _ _ _ _ _ _ a
  cases IsLinearPreorder.le_total (0 : R) a with
  | inl h => exact f.mpr (.inl ⟨h, h⟩)
  | inr h => exact f.mpr (.inr ⟨h, h⟩)

/-- Every finite sum of squares belongs to the weakly nonnegative cone. -/
def SumOfSquares : Prop := ∀ {R : Type u} [Ring R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] (xs : List R),
    (0 : R) ≤ xs.foldr (fun x total => x^2 + total) (0 : R)

theorem sumsOfSquares (f : type_of% @OrderedRing.sq_nonneg.{u}) : SumOfSquares.{u} := by
  intro R _ _ _ _ _ _ xs
  induction xs with
  | nil => exact IsPreorder.le_refl (0 : R)
  | cons x xs ih =>
    have step := (OrderedAdd.add_le_left_iff (xs.foldr (fun x s => x^2 + s) (0 : R))).mp (f (a := x))
    rw [AddCommMonoid.zero_add] at step
    exact IsPreorder.le_trans _ _ _ ih step

def witnesses : List (Name × (Name × Name)) := [
  (``Field.IsOrdered.mul_le_mul_iff_of_pos_left, ``PositiveMultipliers, ``fromPosLeft),
  (``Field.IsOrdered.mul_le_mul_iff_of_pos_right, ``PositiveMultipliers, ``fromPosRight),
  (``Field.IsOrdered.mul_le_mul_iff_of_neg_left, ``PositiveMultipliers, ``fromNegLeft),
  (``Field.IsOrdered.mul_le_mul_iff_of_neg_right, ``PositiveMultipliers, ``fromNegRight),
  (``Field.IsOrdered.le_mul_inv_iff_mul_le, ``PositiveMultipliers, ``fromDivision),
  (``Field.IsOrdered.le_mul_inv_iff_le_mul_of_neg, ``PositiveMultipliers, ``fromNegativeDivision),
  (``Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg, ``PositiveMultipliers, ``fromNegativeDivisionLeft),
  (``Field.IsOrdered.inv_nonpos_iff, ``OppositeSigns, ``fromInverseNonpos),
  (``Field.IsOrdered.inv_nonneg_iff, ``OppositeSigns, ``fromInverseNonneg),
  (``OrderedRing.mul_le_mul_of_nonneg_left, ``NonnegativeProducts, ``fromLeft),
  (``OrderedRing.mul_le_mul_of_nonneg_right, ``NonnegativeProducts, ``fromRight),
  (``OrderedRing.mul_le_mul_of_nonpos_left, ``NonnegativeProducts, ``fromLeftNeg),
  (``OrderedRing.mul_le_mul_of_nonpos_right, ``NonnegativeProducts, ``fromRightNeg),
  (``OrderedRing.mul_nonneg_of_nonpos_of_nonpos, ``NonnegativeProducts, ``fromTwoNonpositive),
  (``OrderedRing.mul_nonpos_of_nonneg_of_nonpos, ``NonnegativeProducts, ``fromMixedRight),
  (``OrderedRing.mul_nonpos_of_nonpos_of_nonneg, ``NonnegativeProducts, ``fromMixedLeft),
  (``OrderedRing.mul_nonneg, ``SignedSquare, ``signedSquareOfProduct),
  (``OrderedRing.mul_nonneg_iff, ``LinearSquare, ``squareOfProductSigns),
  (``OrderedRing.sq_nonneg, ``SumOfSquares, ``sumsOfSquares)]

private theorem notLTOfDoubleNegLE {α : Type u} [LE α] [LT α] [LawfulOrderLT α]
    {a b : α} (h : ¬¬ b ≤ a) : ¬ a < b :=
  fun lt => h ((LawfulOrderLT.lt_iff _ _).mp lt).2

private theorem doubleNegLE {α : Type u} [LE α] [LT α] [LawfulOrderLT α] [IsLinearPreorder α]
    {a b : α} (h : ¬ a < b) : ¬¬ b ≤ a := by
  intro no
  rcases IsLinearPreorder.le_total a b with le | le
  · exact h ((LawfulOrderLT.lt_iff _ _).mpr ⟨le, no⟩)
  · exact no le

/-- Double-negation stability of comparison in a linearly preordered ring. -/
def StableRingLE : Prop := ∀ {α : Type u} [LE α] [LT α] [LawfulOrderLT α] [IsLinearPreorder α]
  [Ring α] [OrderedRing α] (a b : α), ¬¬ a ≤ b → a ≤ b

attribute [local instance] Ring.intCast Semiring.natCast

theorem offsetRule : (type_of% @Grind.Order.le_of_not_lt_k.{u}) ↔ StableRingLE.{u} := by
  constructor
  · intro rule α _ _ _ _ _ _ a b h
    have shift (z : α) : z + ((0 : Int) : α) = z :=
      (congrArg (z + ·) Ring.intCast_zero).trans (Semiring.add_zero z)
    have order := rule (a := b) (b := a) (k := 0) (k' := 0) rfl
    rw [shift, shift] at order
    exact order (notLTOfDoubleNegLE h)
  · intro stable α _ _ _ _ _ _ a b k k' cert denied
    have same : k' = -k := eq_of_beq ((Int.beq'_eq_beq _ _).symm ▸ cert)
    subst k'
    have h := OrderedAdd.add_le_left (stable _ _ (doubleNegLE denied)) (- (k : α))
    rwa [Semiring.add_assoc, AddCommGroup.add_neg_cancel, Semiring.add_zero, ← Ring.intCast_neg] at h

/-- Double-negation stability of the nonpositive cone in a linearly ordered integer module. -/
def StableModuleCone : Prop := ∀ {α : Type u} [IntModule α] [LE α] [LT α] [LawfulOrderLT α]
  [IsLinearOrder α] [OrderedAdd α] (a : α), ¬¬ a ≤ 0 → a ≤ 0

theorem linearRule : (type_of% @Linarith.not_lt_norm.{u}) ↔ StableModuleCone.{u} := by
  constructor
  · intro rule α _ _ _ _ _ _ a h
    exact rule (.leaf a) .zero (.var 0) (.add 1 0 .nil) rfl (notLTOfDoubleNegLE h)
  · intro stable α _ _ _ _ _ _ ctx lhs rhs p cert denied
    apply stable
    exact fun no => doubleNegLE denied (fun le => no (Linarith.le_norm ctx rhs lhs p cert le))

/-- Double-negation stability of the nonpositive cone in a linearly ordered commutative ring. -/
def StableCommRingCone : Prop := ∀ {α : Type u} [CommRing α] [LE α] [LT α] [LawfulOrderLT α]
  [IsLinearOrder α] [OrderedRing α] (a : α), ¬¬ a ≤ 0 → a ≤ 0

theorem commRingRule : (type_of% @CommRing.not_lt_norm.{u}) ↔ StableCommRingCone.{u} := by
  constructor
  · intro rule α _ _ _ _ _ _ a h
    have result := rule (.leaf a) (.num 0) (.var 0) (CommRing.Poly.ofVar 0) rfl (notLTOfDoubleNegLE h)
    rw [CommRing.Poly.denote_ofVar] at result
    exact result
  · intro stable α _ _ _ _ _ _ ctx lhs rhs p cert denied
    apply stable
    exact fun no => doubleNegLE denied (fun le => no (CommRing.le_norm ctx rhs lhs p cert le))

def stabilityEquivalences : List (Name × Name × Name) := [
  (``Grind.Order.le_of_not_lt_k, ``StableRingLE, ``offsetRule),
  (``Linarith.not_lt_norm, ``StableModuleCone, ``linearRule),
  (``CommRing.not_lt_norm, ``StableCommRingCone, ``commRingRule)]

end WeakRingOrder

namespace NaturalCancellation

open Nat.Internal.Linear

/-- Two slots in the official linear expression evaluator. -/
private abbrev pairCtx (a b : Nat) : Context := .branch 1 (.leaf a) (.leaf b)
private abbrev plusOne (i : Nat) : Nat.Internal.Linear.Expr := .add (.var i) (.num 1)

/-- Removing one successor from each side preserves the proposition itself. -/
def SuccLeEq := ∀ a b : Nat, (a.succ ≤ b.succ) = (a ≤ b)

theorem exprEq (rule : type_of% @Expr.of_cancel_eq) : type_of% @Nat.succ.injEq := by
  intro a b
  exact rule (pairCtx a b) (plusOne 0) (plusOne 1) (.var 0) (.var 1) rfl

theorem exprLe (rule : type_of% @Expr.of_cancel_le) : SuccLeEq := by
  intro a b
  exact rule (pairCtx a b) (plusOne 0) (plusOne 1) (.var 0) (.var 1) rfl

theorem exprNormEq (rule : type_of% @ExprCnstr.eq_of_toNormPoly_eq) : type_of% @Nat.succ.injEq := by
  intro a b
  exact rule (pairCtx a b) ⟨true, plusOne 0, plusOne 1⟩ ⟨true, .var 0, .var 1⟩ rfl

theorem exprNorm (rule : type_of% @ExprCnstr.denote_toNormPoly) : type_of% @Nat.succ.injEq := by
  intro a b
  have h := (rule (pairCtx a b) ⟨true, plusOne 0, plusOne 1⟩).symm
  change (a.succ = b.succ) = (1 * a = 1 * b) at h
  rwa [Nat.one_mul, Nat.one_mul] at h

private abbrev polyPlus (i : Nat) : Poly := [(1, i), (1, fixedVar)]

theorem polyEq (rule : type_of% @Poly.denote_eq_cancel_eq) : type_of% @Nat.succ.injEq := by
  intro a b
  have h := (rule (pairCtx a b) (polyPlus 0) (polyPlus 1)).symm
  change ((1 * a) + 1 = (1 * b) + 1) = (1 * a = 1 * b) at h
  rwa [Nat.one_mul, Nat.one_mul] at h

theorem polyLe (rule : type_of% @Poly.denote_le_cancel_eq) : SuccLeEq := by
  intro a b
  have h := (rule (pairCtx a b) (polyPlus 0) (polyPlus 1)).symm
  change ((1 * a) + 1 ≤ (1 * b) + 1) = (1 * a ≤ 1 * b) at h
  rwa [Nat.one_mul, Nat.one_mul] at h


/-- Strict comparison reflects the same successor cancellation. -/
def SuccLtEq := ∀ a b : Nat, (a.succ < b.succ) = (a < b)

theorem exprLt (rule : type_of% @Expr.of_cancel_lt) : SuccLtEq := by
  intro a b
  exact rule (pairCtx a b) (plusOne 0) (plusOne 1) (.var 0) (.var 1) rfl

end NaturalCancellation

namespace NaturalCertificates

open Nat.Internal.Linear

/- The pinned `Poly.isZero` uses a general bitwise operation in its wildcard matcher.
Only its two list-constructor equations enter these proofs. -/
variable (zeroTest : Poly → Bool) (nilTest : zeroTest [] = true)
  (consTest : ∀ head tail, zeroTest (head :: tail) = false)

abbrev valid (c : PolyCnstr) :=
  bif c.eq then zeroTest c.lhs && zeroTest c.rhs else zeroTest c.lhs

abbrev unsat (c : PolyCnstr) :=
  bif c.eq then (zeroTest c.lhs && c.rhs.isNonZero) || (c.lhs.isNonZero && zeroTest c.rhs)
  else c.lhs.isNonZero && zeroTest c.rhs

abbrev ValidRule := ∀ (ctx : Context) {c : PolyCnstr}, valid zeroTest c = true → c.denote ctx = True
abbrev UnsatRule := ∀ (ctx : Context) {c : PolyCnstr}, unsat zeroTest c = true → c.denote ctx = False

/-- The empty polynomial compares with zero and with every nonnegative value. -/
def ZeroTrue := ((0 : Nat) = 0) = True ∧ ∀ n : Nat, (0 ≤ n) = True

/-- A positive polynomial can occur on either side of equality, or below zero. -/
def PositiveFalse := ∀ n : Nat,
  ((0 = n.succ) = False) ∧ ((n.succ = 0) = False) ∧ ((n.succ ≤ 0) = False)

private theorem andParts (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | contradiction

private theorem orParts (a b : Bool) (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> first | exact .inl rfl | exact .inr rfl | contradiction

include consTest in
private theorem zeroValue (ctx : Context) (p : Poly) (h : zeroTest p = true) : p.denote ctx = 0 := by
  cases p with
  | nil => rfl
  | cons term tail => exact Bool.noConfusion ((consTest term tail).symm.trans h)

private theorem positiveValue (ctx : Context) (p : Poly) (h : p.isNonZero = true) : 0 < p.denote ctx := by
  induction p with
  | nil => contradiction
  | cons term tail ih =>
    obtain ⟨k, v⟩ := term
    change (bif v == fixedVar then decide (k > 0) else Poly.isNonZero tail) = true at h
    change 0 < k * Var.denote ctx v + Poly.denote ctx tail
    cases fixed : (v == fixedVar) with
    | true =>
      rw [fixed] at h
      have val : Var.denote ctx v = 1 := congrArg (Bool.rec (motive := fun _ => Nat) (ctx.get v) 1) fixed
      rw [val, Nat.mul_one]
      exact Nat.lt_of_lt_of_le (of_decide_eq_true h) (Nat.le_add_right ..)
    | false =>
      rw [fixed] at h
      exact Nat.lt_of_lt_of_le (ih h) (Nat.le_add_left ..)

private abbrev literal (n : Nat) : Poly := [(n, fixedVar)]
private theorem literalValue (n : Nat) : (literal n).denote (.leaf 0) = n := Nat.mul_one n

include nilTest consTest in
theorem validCertificateIff : ValidRule zeroTest ↔ ZeroTrue := by
  constructor
  · intro rule
    refine ⟨rule (.leaf 0) (c := ⟨true, [], []⟩) (by
      change (zeroTest [] && zeroTest []) = true
      rw [nilTest]
      rfl), fun n => ?_⟩
    have result := rule (.leaf 0) (c := ⟨false, [], literal n⟩) nilTest
    change (0 ≤ (literal n).denote (.leaf 0)) = True at result
    rwa [literalValue] at result
  · intro tags ctx c cert
    obtain ⟨kind, l, r⟩ := c
    cases kind with
    | false =>
      change (l.denote ctx ≤ r.denote ctx) = True
      rw [zeroValue zeroTest consTest ctx l cert]
      exact tags.2 _
    | true =>
      have both := andParts (zeroTest l) (zeroTest r) cert
      change (l.denote ctx = r.denote ctx) = True
      rw [zeroValue zeroTest consTest ctx l both.1, zeroValue zeroTest consTest ctx r both.2]
      exact tags.1

include nilTest consTest in
theorem unsatCertificateIff : UnsatRule zeroTest ↔ PositiveFalse := by
  constructor
  · intro rule n
    have pos : (literal n.succ).isNonZero = true := decide_eq_true (Nat.zero_lt_succ n)
    have left := rule (.leaf 0) (c := ⟨true, [], literal n.succ⟩) (by
      change (zeroTest [] && (literal n.succ).isNonZero || false && zeroTest (literal n.succ)) = true
      rw [nilTest, pos]
      rfl)
    have right := rule (.leaf 0) (c := ⟨true, literal n.succ, []⟩) (by
      change (zeroTest (literal n.succ) && false || (literal n.succ).isNonZero && zeroTest []) = true
      rw [nilTest, consTest, pos]
      rfl)
    have order := rule (.leaf 0) (c := ⟨false, literal n.succ, []⟩) (by
      change ((literal n.succ).isNonZero && zeroTest []) = true
      rw [nilTest, pos]
      rfl)
    change (0 = (literal n.succ).denote (.leaf 0)) = False at left
    change ((literal n.succ).denote (.leaf 0) = 0) = False at right
    change ((literal n.succ).denote (.leaf 0) ≤ 0) = False at order
    rw [literalValue] at left right order
    exact ⟨left, right, order⟩
  · intro tags ctx c cert
    obtain ⟨kind, l, r⟩ := c
    have positive (p : Poly) (h : p.isNonZero = true) : ∃ n : Nat, p.denote ctx = n.succ := by
      have pos := positiveValue ctx p h
      cases e : p.denote ctx with
      | zero => exact (Nat.ne_zero_of_lt pos e).elim
      | succ n => exact ⟨n, rfl⟩
    cases kind with
    | false =>
      have both := andParts l.isNonZero (zeroTest r) cert
      obtain ⟨n, e⟩ := positive l both.1
      change (l.denote ctx ≤ r.denote ctx) = False
      rw [e, zeroValue zeroTest consTest ctx r both.2]
      exact (tags n).2.2
    | true =>
      change (l.denote ctx = r.denote ctx) = False
      cases orParts _ _ cert with
      | inl both =>
        have parts := andParts (zeroTest l) r.isNonZero both
        obtain ⟨n, e⟩ := positive r parts.2
        rw [zeroValue zeroTest consTest ctx l parts.1, e]
        exact (tags n).1
      | inr both =>
        have parts := andParts l.isNonZero (zeroTest r) both
        obtain ⟨n, e⟩ := positive l parts.1
        rw [e, zeroValue zeroTest consTest ctx r parts.2]
        exact (tags n).2.1

/-- Ordinary official imports reduce the empty test on both list constructors. -/
theorem validIff : (type_of% @PolyCnstr.eq_true_of_isValid) ↔ ZeroTrue :=
  validCertificateIff Poly.isZero rfl (fun _ _ => rfl)

theorem unsatIff : (type_of% @PolyCnstr.eq_false_of_isUnsat) ↔ PositiveFalse :=
  unsatCertificateIff Poly.isZero rfl (fun _ _ => rfl)

/-- Cancelling identical variables produces a zero polynomial on both sides. -/
def ReflexiveTrue := ∀ n : Nat, ((n = n) = True) ∧ ((n ≤ n) = True)

/-- Cancelling a variable from its successor leaves the constant one. -/
def SuccessorFalse := ∀ n : Nat,
  ((n.succ = n) = False) ∧ ((n = n.succ) = False) ∧ ((n.succ ≤ n) = False)

include nilTest in
theorem exprValid (rule : ∀ (ctx : Context) (c : ExprCnstr),
    valid zeroTest c.toNormPoly = true → c.denote ctx = True) : ReflexiveTrue := by
  intro n
  have both : (zeroTest [] && zeroTest []) = true := by rw [nilTest]; rfl
  exact ⟨rule (.leaf n) ⟨true, .var 0, .var 0⟩ both,
    rule (.leaf n) ⟨false, .var 0, .var 0⟩ nilTest⟩

include nilTest consTest in
theorem exprUnsat (rule : ∀ (ctx : Context) (c : ExprCnstr),
    unsat zeroTest c.toNormPoly = true → c.denote ctx = False) : SuccessorFalse := by
  intro n
  let x : Nat.Internal.Linear.Expr := .var 0
  let succ : Nat.Internal.Linear.Expr := .add x (.num 1)
  have positiveLeft : (zeroTest [(1, fixedVar)] && false || true && zeroTest []) = true := by
    rw [nilTest, consTest]
    rfl
  have positiveRight : (zeroTest [] && true || false && zeroTest [(1, fixedVar)]) = true := by
    rw [nilTest]
    rfl
  have order : (true && zeroTest []) = true := by rw [nilTest]; rfl
  exact ⟨rule (.leaf n) ⟨true, succ, x⟩ positiveLeft,
    rule (.leaf n) ⟨true, x, succ⟩ positiveRight, rule (.leaf n) ⟨false, succ, x⟩ order⟩

theorem ofExprValid : (type_of% @ExprCnstr.eq_true_of_isValid) → ReflexiveTrue :=
  exprValid Poly.isZero rfl

theorem ofExprUnsat : (type_of% @ExprCnstr.eq_false_of_isUnsat) → SuccessorFalse :=
  exprUnsat Poly.isZero rfl (fun _ _ => rfl)

end NaturalCertificates

namespace IntegerCancellation

open Int.Internal.Linear

private abbrev pairCtx (a b : Int) : Context := .branch 1 (.leaf a) (.leaf b)
private abbrev plusOne (i : Nat) : Int.Internal.Linear.Expr := .add (.var i) (.num 1)
def AddOneEq := ∀ a b : Int, (a + 1 = b + 1) = (a = b)
def AddOneLE := ∀ a b : Int, (a + 1 ≤ b + 1) = (a ≤ b)
private abbrev difference : Poly := .add (-1) 1 (.add 1 0 (.num 0))


theorem eqVar (rule : type_of% @norm_eq_var) : AddOneEq := by
  intro a b
  exact rule (pairCtx b a) (plusOne 1) (plusOne 0) 1 0 rfl

theorem eqNorm (rule : type_of% @norm_eq) : AddOneEq := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference rfl).symm

theorem leNorm (rule : type_of% @norm_le) : AddOneLE := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference rfl).symm

theorem eqCoeff (rule : type_of% @norm_eq_coeff) : AddOneEq := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference 1 rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference 1 rfl).symm

theorem leCoeff (rule : type_of% @norm_le_coeff) : AddOneLE := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference 1 rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference 1 rfl).symm

/-- Cancelling a common factor in a divisibility proposition preserves that proposition's identity. -/
def DoubledDivisibility := ∀ x : Int, ((2 : Int) ∣ 2 * x) = ((1 : Int) ∣ x)

theorem doubledDivisibility (rule : type_of% @norm_dvd_gcd) : DoubledDivisibility :=
  fun x => rule (.leaf x) 2 (.mulL 2 (.var 0)) 1 (.add 1 0 (.num 0)) 2 rfl

/-- The normalization rule identifies each impossible successor equality with falsity. -/
def SuccessorFalse := ∀ z : Int, (z = z + 1) = False

theorem successorFalse (rule : type_of% @eq_eq_false) : SuccessorFalse :=
  fun z => rule (.leaf z) (.var 0) (.add (.var 0) (.num 1)) rfl

def ZeroOneFalse := ((0 : Int) = 1) = False

theorem zeroOneFalse (rule : type_of% @eq_eq_false_of_divCoeff) : ZeroOneFalse :=
  rule (.leaf 0) (.num 0) (.num 1) 2 rfl

def TwoDividesOneFalse := ((2 : Int) ∣ 1) = False

theorem twoDividesOneFalse (rule : type_of% @dvd_eq_false) : TwoDividesOneFalse :=
  rule (.leaf 0) 2 (.num 1) rfl

def AddOneEqOne := ∀ a : Int, (a + 1 = 1) = (a = 0)

theorem addOneEqOne (rule : type_of% @norm_eq_var_const) : AddOneEqOne :=
  fun a => rule (.leaf a) (.add (.var 0) (.num 1)) (.num 1) 0 0 rfl

/-- Normalizing a variable against itself leaves the constant zero. -/
def ReflexiveEq := ∀ z : Int, (z = z) = True

def ReflexiveLE := ∀ z : Int, (z ≤ z) = True

/-- Normalizing a successor against the original variable leaves the constant one. -/
def SuccessorLEFalse := ∀ z : Int, (z + 1 ≤ z) = False

theorem reflexiveEqOfTest (test : Poly → Bool) (zero : test (.num 0) = true)
    (rule : ∀ (ctx : Context) (lhs rhs : Int.Internal.Linear.Expr),
      test (lhs.sub rhs).norm = true → (lhs.denote ctx = rhs.denote ctx) = True) : ReflexiveEq :=
  fun z => rule (.leaf z) (.var 0) (.var 0) zero

theorem reflexiveLEOfTest (test : Poly → Bool) (zero : test (.num 0) = true)
    (rule : ∀ (ctx : Context) (lhs rhs : Int.Internal.Linear.Expr),
      test (lhs.sub rhs).norm = true → (lhs.denote ctx ≤ rhs.denote ctx) = True) : ReflexiveLE :=
  fun z => rule (.leaf z) (.var 0) (.var 0) zero

theorem successorLEOfTest (test : Poly → Bool) (one : test (.num 1) = true)
    (rule : ∀ (ctx : Context) (lhs rhs : Int.Internal.Linear.Expr),
      test (lhs.sub rhs).norm = true → (lhs.denote ctx ≤ rhs.denote ctx) = False) : SuccessorLEFalse :=
  fun z => rule (.leaf z) (plusOne 0) (.var 0) one

theorem ofValidEq : (type_of% @eq_eq_true) → ReflexiveEq :=
  reflexiveEqOfTest Poly.isValidEq rfl

theorem ofValidLE : (type_of% @le_eq_true) → ReflexiveLE :=
  reflexiveLEOfTest Poly.isValidLe rfl

theorem ofUnsatLE : (type_of% @le_eq_false) → SuccessorLEFalse :=
  successorLEOfTest Poly.isUnsatLe rfl

/-- Tightening an odd bound divides by two and rounds its constant upward. -/
def OddBound := ∀ a : Int, (2 * a + 1 ≤ 0) = (a + 1 ≤ 0)

theorem oddBound (rule : type_of% @norm_le_coeff_tight) : OddBound :=
  fun a => rule (.leaf a) (.add (.mulL 2 (.var 0)) (.num 1)) (.num 0) (.add 1 0 (.num 1)) 2 rfl

def LiteralReflection := ∀ a b : Int, (a.beq' b = true) = (Poly.num a = Poly.num b)

theorem literalReflection (rule : type_of% @Poly.beq'_eq) : LiteralReflection :=
  fun a b => rule (.num a) (.num b)

def witnesses : List (Name × Name × Name) := [
  (``norm_eq_var_const, ``AddOneEqOne, ``addOneEqOne),
  (``norm_le_coeff_tight, ``OddBound, ``oddBound),
  (``Poly.beq'_eq, ``LiteralReflection, ``literalReflection),
  (``norm_dvd_gcd, ``DoubledDivisibility, ``doubledDivisibility),
  (``eq_eq_false, ``SuccessorFalse, ``successorFalse),
  (``eq_eq_false_of_divCoeff, ``ZeroOneFalse, ``zeroOneFalse),
  (``dvd_eq_false, ``TwoDividesOneFalse, ``twoDividesOneFalse)]

end IntegerCancellation

open Nat.Internal.Linear Int.Internal.Linear NaturalCertificates IntegerCancellation in
/-- Each row gives the official site, consequence, specialized proof and the proof over an
arbitrary Boolean test. Empty-kernel replay uses the latter because the official matcher
carries an axiom dependency in the implementation of its constructor mask. -/
def linearCertificates : List (Name × Name × Name × Name) := [
  (``PolyCnstr.eq_true_of_isValid, ``ZeroTrue, ``validIff, ``validCertificateIff),
  (``PolyCnstr.eq_false_of_isUnsat, ``PositiveFalse, ``unsatIff, ``unsatCertificateIff),
  (``ExprCnstr.eq_true_of_isValid, ``ReflexiveTrue, ``ofExprValid, ``exprValid),
  (``ExprCnstr.eq_false_of_isUnsat, ``NaturalCertificates.SuccessorFalse, ``ofExprUnsat, ``exprUnsat),
  (``eq_eq_true, ``ReflexiveEq, ``ofValidEq, ``reflexiveEqOfTest),
  (``le_eq_true, ``ReflexiveLE, ``ofValidLE, ``reflexiveLEOfTest),
  (``le_eq_false, ``SuccessorLEFalse, ``ofUnsatLE, ``successorLEOfTest)]

end OmegaChecks.InitBoundaries
