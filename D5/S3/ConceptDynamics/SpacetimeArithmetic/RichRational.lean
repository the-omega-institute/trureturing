/- GID: D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeArithmetic/RichRational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pairs of balanced archives carry guarded rational arithmetic through exact readout. -/

import D5.S3.ConceptDynamics.Spacetime.ParallelComposition
import D5.S3.ConceptDynamics.Spacetime.GeneratedProduct
import D5.S3.ConceptDynamics.Spacetime.ComplementFibers
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeArithmetic.RichRational

open Spacetime.ComplementCharge Spacetime.ComplementFibers
open Spacetime.ParallelComposition Spacetime.GeneratedProduct

noncomputable section
variable {d : Nat}

/-- Both components are actual balanced histories; the guard concerns the denominator. -/
structure Fraction (d : Nat) where
  numerator : BalancedRich d
  denominator : BalancedRich d
  denominator_ne_zero : balancedQ denominator ≠ 0

def readout (r : Fraction d) : Rat :=
  (balancedQ r.numerator : Rat) / (balancedQ r.denominator : Rat)

def CrossEquivalent (r s : Fraction d) : Prop :=
  balancedQ r.numerator * balancedQ s.denominator =
    balancedQ s.numerator * balancedQ r.denominator

theorem denominator_cast_ne_zero (r : Fraction d) :
    (balancedQ r.denominator : Rat) ≠ 0 := by
  exact_mod_cast r.denominator_ne_zero

theorem cross_iff_readout (r s : Fraction d) :
    CrossEquivalent r s ↔ readout r = readout s := by
  rw [readout, readout, div_eq_div_iff (denominator_cast_ne_zero r)
    (denominator_cast_ne_zero s)]
  unfold CrossEquivalent
  exact_mod_cast (Iff.rfl :
    balancedQ r.numerator * balancedQ s.denominator =
        balancedQ s.numerator * balancedQ r.denominator ↔
    balancedQ r.numerator * balancedQ s.denominator =
        balancedQ s.numerator * balancedQ r.denominator)

/-- The standard kernel setoid is on the full history-pair carrier. -/
def kernelSetoid (d : Nat) : Setoid (Fraction d) := Setoid.ker readout

theorem kernel_iff_cross (r s : Fraction d) :
    kernelSetoid d r s ↔ CrossEquivalent r s := (cross_iff_readout r s).symm

theorem cross_equivalence : Equivalence (CrossEquivalent : Fraction d → Fraction d → Prop) := by
  have hrel : (fun r s : Fraction d => kernelSetoid d r s) = CrossEquivalent :=
    funext fun r => funext fun s => propext (kernel_iff_cross r s)
  rw [← hrel]
  exact (kernelSetoid d).iseqv

def InverseGuard (r : Fraction d) : Prop := balancedQ r.numerator ≠ 0

def DivisionGuard (s : Fraction d) : Prop := balancedQ s.numerator ≠ 0

theorem inverse_guard_iff (r : Fraction d) : InverseGuard r ↔ readout r ≠ 0 := by
  simp [InverseGuard, readout, r.denominator_ne_zero]

theorem division_guard_iff (s : Fraction d) : DivisionGuard s ↔ readout s ≠ 0 :=
  inverse_guard_iff s

theorem inverse_guard_congr {r s : Fraction d} (h : CrossEquivalent r s) :
    InverseGuard r ↔ InverseGuard s := by
  rw [inverse_guard_iff, inverse_guard_iff, (cross_iff_readout r s).mp h]

theorem division_guard_congr {r s : Fraction d} (h : CrossEquivalent r s) :
    DivisionGuard r ↔ DivisionGuard s := inverse_guard_congr h

/-- The numerator retains the ordered parallel composition of the two cross-products. -/
def add (r s : Fraction d) : Fraction d where
  numerator := parallelBalanced (productBalanced r.numerator s.denominator)
    (productBalanced s.numerator r.denominator)
  denominator := productBalanced r.denominator s.denominator
  denominator_ne_zero := by
    change q (product r.denominator.val s.denominator.val) ≠ 0
    rw [q_product]
    exact mul_ne_zero r.denominator_ne_zero s.denominator_ne_zero

def mul (r s : Fraction d) : Fraction d where
  numerator := productBalanced r.numerator s.numerator
  denominator := productBalanced r.denominator s.denominator
  denominator_ne_zero := (add r s).denominator_ne_zero

def neg (r : Fraction d) : Fraction d where
  numerator := complementBalanced r.numerator
  denominator := r.denominator
  denominator_ne_zero := r.denominator_ne_zero

def inv (r : Fraction d) (h : InverseGuard r) : Fraction d where
  numerator := r.denominator
  denominator := r.numerator
  denominator_ne_zero := h

def div (r s : Fraction d) (h : DivisionGuard s) : Fraction d where
  numerator := productBalanced r.numerator s.denominator
  denominator := productBalanced r.denominator s.numerator
  denominator_ne_zero := by
    change q (product r.denominator.val s.numerator.val) ≠ 0
    rw [q_product]
    exact mul_ne_zero r.denominator_ne_zero h

theorem add_readout (r s : Fraction d) : readout (add r s) = readout r + readout s := by
  change (q (parallel (product r.numerator.val s.denominator.val)
    (product s.numerator.val r.denominator.val)) : Rat) /
    (q (product r.denominator.val s.denominator.val) : Rat) = _
  rw [q_parallel, q_product, q_product, q_product, Int.cast_add, Int.cast_mul,
    Int.cast_mul, Int.cast_mul]
  simpa only [readout, balancedQ, mul_comm] using
    (div_add_div (balancedQ r.numerator : Rat) (balancedQ s.numerator : Rat)
      (denominator_cast_ne_zero r) (denominator_cast_ne_zero s)).symm

theorem mul_readout (r s : Fraction d) : readout (mul r s) = readout r * readout s := by
  change (q (product r.numerator.val s.numerator.val) : Rat) /
    (q (product r.denominator.val s.denominator.val) : Rat) = _
  rw [q_product, q_product, Int.cast_mul, Int.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem neg_readout (r : Fraction d) : readout (neg r) = -readout r := by
  change (q (complementBalanced r.numerator).val : Rat) /
    (balancedQ r.denominator : Rat) = _
  rw [complementBalanced_readout, Int.cast_neg, neg_div]
  rfl

theorem inv_readout (r : Fraction d) (h : InverseGuard r) :
    readout (inv r h) = (readout r)⁻¹ := by
  exact (inv_div _ _).symm

theorem div_readout (r s : Fraction d) (h : DivisionGuard s) :
    readout (div r s h) = readout r / readout s := by
  change (q (product r.numerator.val s.denominator.val) : Rat) /
    (q (product r.denominator.val s.numerator.val) : Rat) = _
  rw [q_product, q_product, Int.cast_mul, Int.cast_mul]
  exact (div_div_div_eq (balancedQ r.numerator : Rat)
    (balancedQ r.denominator : Rat) (balancedQ s.numerator : Rat)
    (balancedQ s.denominator : Rat)).symm

theorem add_congr {r r' s s' : Fraction d}
    (hr : CrossEquivalent r r') (hs : CrossEquivalent s s') :
    CrossEquivalent (add r s) (add r' s') := by
  rw [cross_iff_readout, add_readout, add_readout,
    (cross_iff_readout r r').mp hr, (cross_iff_readout s s').mp hs]

theorem mul_congr {r r' s s' : Fraction d}
    (hr : CrossEquivalent r r') (hs : CrossEquivalent s s') :
    CrossEquivalent (mul r s) (mul r' s') := by
  rw [cross_iff_readout, mul_readout, mul_readout,
    (cross_iff_readout r r').mp hr, (cross_iff_readout s s').mp hs]

theorem neg_congr {r r' : Fraction d} (h : CrossEquivalent r r') :
    CrossEquivalent (neg r) (neg r') := by
  rw [cross_iff_readout, neg_readout, neg_readout, (cross_iff_readout r r').mp h]

theorem inv_congr {r r' : Fraction d} (h : CrossEquivalent r r')
    (hr : InverseGuard r) (hr' : InverseGuard r') :
    CrossEquivalent (inv r hr) (inv r' hr') := by
  rw [cross_iff_readout, inv_readout, inv_readout, (cross_iff_readout r r').mp h]

theorem div_congr {r r' s s' : Fraction d}
    (hr : CrossEquivalent r r') (hs : CrossEquivalent s s')
    (h : DivisionGuard s) (h' : DivisionGuard s') :
    CrossEquivalent (div r s h) (div r' s' h') := by
  rw [cross_iff_readout, div_readout, div_readout,
    (cross_iff_readout r r').mp hr, (cross_iff_readout s s').mp hs]

/-- Integer embedding keeps X literally, and uses the dimension-d representative of one. -/
def integerEmbedding (x : BalancedRich d) : Fraction d where
  numerator := x
  denominator := balancedSection d 1
  denominator_ne_zero := by rw [balancedSection_rightInverse d]; decide

theorem integerEmbedding_readout (x : BalancedRich d) :
    readout (integerEmbedding x) = (balancedQ x : Rat) := by
  change (balancedQ x : Rat) / (balancedQ (balancedSection d 1) : Rat) = _
  rw [balancedSection_rightInverse d]
  simp

theorem integerEmbedding_retains (x : BalancedRich d) :
    (integerEmbedding x).numerator = x := rfl

end
end D5.S3.ConceptDynamics.SpacetimeArithmetic.RichRational
