/- GID: D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative balanced histories modulo readout form the natural semiring. -/

import D5.S3.ConceptDynamics.Spacetime.ComplementFibers
import D5.S3.ConceptDynamics.Spacetime.ParallelComposition
import D5.S3.ConceptDynamics.Spacetime.GeneratedProduct
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Ring.TransferInstance

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeArithmetic.NaturalQuotient

open Spacetime ComplementCharge ComplementFibers ParallelComposition GeneratedProduct
noncomputable section

def NonnegativeHistory (d : Nat) := {x : BalancedRich d // 0 ≤ balancedQ x}

def naturalQ {d : Nat} (x : NonnegativeHistory d) : Nat := (balancedQ x.val).toNat

/-- The conversion to Nat preserves the signed readout on exactly this domain. -/
theorem naturalQ_cast {d : Nat} (x : NonnegativeHistory d) :
    (naturalQ x : Int) = balancedQ x.val := Int.toNat_of_nonneg x.property

def naturalSection (d : Nat) (n : Nat) : NonnegativeHistory d :=
  ⟨balancedSection d n, by rw [balancedSection_rightInverse d]; exact Int.natCast_nonneg n⟩

theorem naturalSection_rightInverse (d : Nat) :
    Function.RightInverse (naturalSection d) (naturalQ : NonnegativeHistory d → Nat) := by
  intro n
  change (balancedQ (balancedSection d (n : Int))).toNat = n
  rw [balancedSection_rightInverse d (n : Int), Int.toNat_natCast]

def numericalSetoid (d : Nat) : Setoid (NonnegativeHistory d) := Setoid.ker naturalQ

theorem numerical_iff_signed {d : Nat} (x y : NonnegativeHistory d) :
    numericalSetoid d x y ↔ balancedQ x.val = balancedQ y.val := by
  change naturalQ x = naturalQ y ↔ _
  constructor
  · intro h
    rw [← naturalQ_cast x, ← naturalQ_cast y, h]
  · intro h
    exact congrArg Int.toNat h

def NaturalHistory (d : Nat) := Quotient (numericalSetoid d)

def classOf {d : Nat} (x : NonnegativeHistory d) : NaturalHistory d := Quotient.mk _ x

theorem class_eq_iff_signed {d : Nat} (x y : NonnegativeHistory d) :
    classOf x = classOf y ↔ balancedQ x.val = balancedQ y.val :=
  Quotient.eq.trans (numerical_iff_signed x y)

def readoutEquiv (d : Nat) : NaturalHistory d ≃ Nat :=
  Setoid.quotientKerEquivOfRightInverse naturalQ (naturalSection d)
    (naturalSection_rightInverse d)

instance naturalHistoryCommSemiring (d : Nat) : CommSemiring (NaturalHistory d) :=
  (readoutEquiv d).commSemiring

def readoutSemiringEquiv (d : Nat) : NaturalHistory d ≃+* Nat :=
  (readoutEquiv d).ringEquiv

@[simp] theorem readout_class {d : Nat} (x : NonnegativeHistory d) :
    readoutSemiringEquiv d (classOf x) = naturalQ x := rfl

def parallelNonnegative {d : Nat} (x y : NonnegativeHistory d) : NonnegativeHistory d :=
  ⟨parallelBalanced x.val y.val, by
    change 0 ≤ q (parallel x.val.val y.val.val)
    rw [q_parallel]
    exact add_nonneg x.property y.property⟩

def productNonnegative {d : Nat} (x y : NonnegativeHistory d) : NonnegativeHistory d :=
  ⟨productBalanced x.val y.val, by
    change 0 ≤ q (product x.val.val y.val.val)
    rw [q_product]
    exact Int.mul_nonneg x.property y.property⟩

theorem zero_class (d : Nat) :
    (0 : NaturalHistory d) = classOf (naturalSection d 0) := rfl

theorem one_class (d : Nat) :
    (1 : NaturalHistory d) = classOf (naturalSection d 1) := rfl

theorem add_class {d : Nat} (x y : NonnegativeHistory d) :
    classOf x + classOf y = classOf (parallelNonnegative x y) := by
  apply (readoutSemiringEquiv d).injective
  rw [map_add, readout_class, readout_class, readout_class]
  apply Int.ofNat_inj.mp
  rw [Int.natCast_add, naturalQ_cast, naturalQ_cast, naturalQ_cast]
  exact (q_parallel x.val.val y.val.val).symm

theorem mul_class {d : Nat} (x y : NonnegativeHistory d) :
    classOf x * classOf y = classOf (productNonnegative x y) := by
  apply (readoutSemiringEquiv d).injective
  rw [map_mul, readout_class, readout_class, readout_class]
  apply Int.ofNat_inj.mp
  rw [Int.natCast_mul, naturalQ_cast, naturalQ_cast, naturalQ_cast]
  exact (q_product x.val.val y.val.val).symm

theorem readout_unique {d : Nat} (f : NaturalHistory d → Nat)
    (hf : ∀ x : NonnegativeHistory d, f (classOf x) = naturalQ x) :
    f = readoutSemiringEquiv d := by
  funext z
  exact Quotient.inductionOn z hf

/-- Native complement stays in the nonnegative domain only at readout zero. -/
theorem complement_nonnegative_iff {d : Nat} (x : NonnegativeHistory d) :
    0 ≤ balancedQ (complementBalanced x.val) ↔ balancedQ x.val = 0 := by
  change 0 ≤ q (complementBalanced x.val).val ↔ _
  rw [complementBalanced_readout]
  have hx := x.property
  change 0 ≤ q x.val.val at hx
  change -q x.val.val ≥ 0 ↔ q x.val.val = 0
  omega

theorem complement_not_closed (d : Nat) :
    ¬ ∀ x : NonnegativeHistory d, 0 ≤ balancedQ (complementBalanced x.val) := by
  intro h
  have hz := (complement_nonnegative_iff (naturalSection d 1)).mp (h _)
  change balancedQ (balancedSection d 1) = 0 at hz
  rw [balancedSection_rightInverse d] at hz
  exact Int.one_ne_zero hz

end
end D5.S3.ConceptDynamics.SpacetimeArithmetic.NaturalQuotient
