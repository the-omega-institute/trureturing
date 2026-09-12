/- GID: D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced archived histories modulo signed readout form the integer ring. -/

import D5.S3.ConceptDynamics.Spacetime.ComplementFibers
import D5.S3.ConceptDynamics.Spacetime.ParallelComposition
import D5.S3.ConceptDynamics.Spacetime.GeneratedProduct
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Ring.TransferInstance

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeArithmetic.IntegerQuotient

open D5.S0.History.Spacetime.ArchiveCarrier
open Spacetime ComplementCharge ComplementFibers ParallelComposition GeneratedProduct
noncomputable section

/-- The kernel is taken on the actual balanced rich-history subtype. -/
def numericalSetoid (d : Nat) : Setoid (BalancedRich d) := Setoid.ker balancedQ

def IntegerHistory (d : Nat) := Quotient (numericalSetoid d)

def classOf {d : Nat} (x : BalancedRich d) : IntegerHistory d := Quotient.mk _ x

def readoutEquiv (d : Nat) : IntegerHistory d ≃ Int :=
  Setoid.quotientKerEquivOfRightInverse balancedQ (balancedSection d)
    (balancedSection_rightInverse d)

theorem class_eq_iff {d : Nat} (x y : BalancedRich d) :
    classOf x = classOf y ↔ balancedQ x = balancedQ y :=
  (readoutEquiv d).injective.eq_iff.symm

/-- Only the quotient receives ring structure; neither raw carrier has a ring instance. -/
instance integerHistoryCommRing (d : Nat) : CommRing (IntegerHistory d) :=
  (readoutEquiv d).commRing

def readoutRingEquiv (d : Nat) : IntegerHistory d ≃+* Int :=
  (readoutEquiv d).ringEquiv

@[simp] theorem readoutRingEquiv_class {d : Nat} (x : BalancedRich d) :
    readoutRingEquiv d (classOf x) = balancedQ x := rfl

theorem zero_class (d : Nat) :
    (0 : IntegerHistory d) = classOf (balancedSection d 0) := rfl

theorem one_class (d : Nat) :
    (1 : IntegerHistory d) = classOf (balancedSection d 1) := rfl

theorem add_class {d : Nat} (x y : BalancedRich d) :
    classOf x + classOf y = classOf (parallelBalanced x y) := by
  apply (readoutRingEquiv d).injective
  rw [map_add, readoutRingEquiv_class, readoutRingEquiv_class, readoutRingEquiv_class]
  exact (q_parallel x.val y.val).symm

theorem mul_class {d : Nat} (x y : BalancedRich d) :
    classOf x * classOf y = classOf (productBalanced x y) := by
  apply (readoutRingEquiv d).injective
  rw [map_mul, readoutRingEquiv_class, readoutRingEquiv_class, readoutRingEquiv_class]
  exact (q_product x.val y.val).symm

theorem neg_class {d : Nat} (x : BalancedRich d) :
    -classOf x = classOf (complementBalanced x) := by
  apply (readoutRingEquiv d).injective
  rw [map_neg, readoutRingEquiv_class, readoutRingEquiv_class]
  exact (complementBalanced_readout x).symm

theorem parallel_congr {d : Nat} {x x' y y' : BalancedRich d}
    (hx : numericalSetoid d x x') (hy : numericalSetoid d y y') :
    numericalSetoid d (parallelBalanced x y) (parallelBalanced x' y') := by
  apply (class_eq_iff _ _).mp
  rw [← add_class, ← add_class, (class_eq_iff x x').mpr hx, (class_eq_iff y y').mpr hy]

theorem product_congr {d : Nat} {x x' y y' : BalancedRich d}
    (hx : numericalSetoid d x x') (hy : numericalSetoid d y y') :
    numericalSetoid d (productBalanced x y) (productBalanced x' y') := by
  apply (class_eq_iff _ _).mp
  rw [← mul_class, ← mul_class, (class_eq_iff x x').mpr hx, (class_eq_iff y y').mpr hy]

theorem complement_congr {d : Nat} {x y : BalancedRich d}
    (h : numericalSetoid d x y) :
    numericalSetoid d (complementBalanced x) (complementBalanced y) := by
  apply (class_eq_iff _ _).mp
  rw [← neg_class, ← neg_class, (class_eq_iff x y).mpr h]

/-- Uniqueness even among functions, with the specified action on every class. -/
theorem readout_unique {d : Nat} (f : IntegerHistory d → Int)
    (hf : ∀ x : BalancedRich d, f (classOf x) = balancedQ x) :
    f = readoutRingEquiv d := by
  funext z
  exact Quotient.inductionOn z hf

theorem readoutRingEquiv_unique {d : Nat} (f : IntegerHistory d ≃+* Int)
    (hf : ∀ x : BalancedRich d, f (classOf x) = balancedQ x) :
    f = readoutRingEquiv d := by
  apply DFunLike.ext
  exact congrFun (readout_unique f hf)

end
end D5.S3.ConceptDynamics.SpacetimeArithmetic.IntegerQuotient
