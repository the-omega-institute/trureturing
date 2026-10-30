/- GID: D5/S3/Analytic/Entire/WeightedHankel
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/WeightedHankel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Removing the quadratic Hankel weight by scalar differentiation on entire functions. -/

import D5.S3.Analytic.Entire.SeparatedKernel
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Scalar differentiation removes the quadratic weight on the whole complex plane. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.Entire

def hankel (f : ℂ → ℂ) : ℂ → ℂ → ℂ := fun z w => f (z + w)

def weightedHankel (f : ℂ → ℂ) : ℂ → ℂ → ℂ :=
  fun z w => (z - w) ^ 2 * f (z + w)

/-- Difference of the two scalar partial derivatives. -/
def differenceDeriv (F : ℂ → ℂ → ℂ) : ℂ → ℂ → ℂ :=
  fun z w => deriv (fun x => F x w) z - deriv (F z) w

theorem FiniteSeparated.difference_deriv {F : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) : FiniteSeparated (differenceDeriv F) :=
  hF.deriv_left.sub hF.deriv_right

/-- Differentiation transverse to the sum variable cancels its derivative. -/
theorem difference_deriv_product {f q : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hq : Differentiable ℂ q) :
    differenceDeriv (fun z w => q (z - w) * f (z + w)) =
      fun z w => 2 * deriv q (z - w) * f (z + w) := by
  funext z w
  have hqL := (hq (z - w)).hasDerivAt.comp z ((hasDerivAt_id z).sub_const w)
  have hfL := (hf (z + w)).hasDerivAt.comp z ((hasDerivAt_id z).add_const w)
  have hqR := (hq (z - w)).hasDerivAt.comp w
    ((hasDerivAt_const w z).sub (hasDerivAt_id w))
  have hfR := (hf (z + w)).hasDerivAt.comp w
    ((hasDerivAt_const w z).add (hasDerivAt_id w))
  change deriv (fun x => q (x - w) * f (x + w)) z -
    deriv (fun x => q (z - x) * f (z + x)) w = _
  have hL := (hqL.mul hfL).deriv
  have hR := (hqR.mul hfR).deriv
  change deriv (fun x => q (x - w) * f (x + w)) z = _ at hL
  change deriv (fun x => q (z - x) * f (z + x)) w = _ at hR
  rw [hL, hR]
  simp only [Function.comp_apply, id_eq]
  ring

theorem difference_deriv_weighted {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    differenceDeriv (weightedHankel f) =
      fun z w => (4 * (z - w)) * f (z + w) := by
  have hd (u : ℂ) : deriv (fun x : ℂ => x ^ 2) u = 2 * u := by
    have h := ((hasDerivAt_id u).pow 2).deriv
    change deriv (fun x : ℂ => x ^ 2) u = (2 : ℂ) * u ^ (2 - 1) * 1 at h
    simpa only [Nat.reduceSub, pow_one, mul_one] using h
  have h := difference_deriv_product (f := f) (q := fun u : ℂ => u ^ 2)
    hf (differentiable_id.pow 2)
  change differenceDeriv (fun z w => (z - w) ^ 2 * f (z + w)) = _
  rw [h]
  funext z w
  rw [hd]
  ring

theorem difference_deriv_twice_weighted {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    differenceDeriv (differenceDeriv (weightedHankel f)) =
      fun z w => 8 * f (z + w) := by
  rw [difference_deriv_weighted hf]
  have hd (u : ℂ) : deriv (fun x : ℂ => 4 * x) u = 4 := by
    have h := ((hasDerivAt_id u).const_mul (4 : ℂ)).deriv
    change deriv (fun x : ℂ => 4 * x) u = (4 : ℂ) * 1 at h
    simpa only [mul_one] using h
  have h := difference_deriv_product (f := f) (q := fun u : ℂ => 4 * u)
    hf (differentiable_id.const_mul (4 : ℂ))
  change differenceDeriv (fun z w => (4 * (z - w)) * f (z + w)) = _
  rw [h]
  funext z w
  rw [hd]
  ring

/-- Finite separation of the quadratic kernel yields finite separation of
the unweighted Hankel kernel on the whole complex plane. -/
theorem finite_separated_hankel_of_weighted {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hF : FiniteSeparated (weightedHankel f)) :
    FiniteSeparated (hankel f) := by
  have h := (hF.difference_deriv.difference_deriv).const_mul (1 / 8 : ℂ)
  rw [difference_deriv_twice_weighted hf] at h
  change FiniteSeparated (fun z w => f (z + w))
  simpa only [← mul_assoc, one_div_mul_cancel (by norm_num : (8 : ℂ) ≠ 0),
    one_mul] using h

/-- The actual complete translate space of f is finite dimensional; the
quadratic factor has not been divided away at its diagonal zero set. -/
theorem finite_translation_space_of_weighted {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hF : FiniteSeparated (weightedHankel f)) :
    FiniteDimensional ℂ (translationSpace f) :=
  finite_translation_space_of_separated_hankel (finite_separated_hankel_of_weighted hf hF)

#print axioms finite_translation_space_of_weighted

end D5.S3.Analytic.Entire
