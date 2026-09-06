/- GID: D5/S3/Quantum/Tomography/HadamardResidualBarrier
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/HadamardResidualBarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every exact common-unbiased root of a nearby order-six matrix lies in an explicitly bounded residual sublevel set of the base matrix. -/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Reuse audit (2026-09-06):
   Repository searches for Hadamard residual perturbation returned no owner.
   The existing CayleyCoverAnalysis already owns generic root migration and
   residual-gap transport; this file supplies only the missing matrix estimate.
   Uses Matrix.mulVec, conjugate transpose, Complex.normSq_eq_norm_sq,
   norm_sum_le and the reverse triangle inequality. No second residual, root,
   Hadamard, interval, or context carrier is introduced.
-/

open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.HadamardResidualBarrier

private theorem normSq_change_of_reference_normSq_six
    (z w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hw : Complex.normSq w = 6) (hzw : ‖z - w‖ ≤ r) :
    |Complex.normSq z - 6| ≤ 5 * r + r ^ 2 := by
  have hwSq : ‖w‖ ^ 2 = 6 := by
    simpa only [Complex.normSq_eq_norm_sq] using hw
  have hwBound : ‖w‖ ≤ (5 / 2 : ℝ) := by
    nlinarith [norm_nonneg w]
  have hzBound : ‖z‖ ≤ r + ‖w‖ := by
    calc
      ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ r + ‖w‖ := add_le_add_right hzw _
  have hReverse : |‖z‖ - ‖w‖| ≤ r :=
    (abs_norm_sub_norm_le z w).trans hzw
  have hSum : ‖z‖ + ‖w‖ ≤ 5 + r := by linarith
  calc
    |Complex.normSq z - 6| = |‖z‖ ^ 2 - ‖w‖ ^ 2| := by
      rw [Complex.normSq_eq_norm_sq, hwSq]
    _ = |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) := by
      rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 =
        (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w))]
    _ ≤ r * (‖z‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_right hReverse (add_nonneg (norm_nonneg z) (norm_nonneg w))
    _ ≤ r * (5 + r) := mul_le_mul_of_nonneg_left hSum hr
    _ = 5 * r + r ^ 2 := by ring

/-- An exact common-unbiased phase vector for H has small residual for H0
whenever each matrix entry changes by at most delta. The estimate uses the
actual target norm squared six, rather than the coarser global norm bound.
Combined with a certified residual-sublevel cover of H0, it prevents new roots
outside the guards for arbitrary nearby Hadamard matrices. It does not assume
that the perturbation remains in the two-circulant or X family. -/
theorem common_unbiased_root_has_small_base_residual
    (H0 H : Matrix (Fin 6) (Fin 6) ℂ) (u : Fin 6 → ℂ)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hu : ∀ i, Complex.normSq (u i) = 1)
    (hnear : ∀ i j, ‖H0 i j - H i j‖ ≤ delta)
    (hroot : ∀ j, Complex.normSq ((Hᴴ *ᵥ u) j) = 6) :
    ∀ j, |Complex.normSq ((H0ᴴ *ᵥ u) j) - 6| ≤
      30 * delta + 36 * delta ^ 2 := by
  have huNorm (i : Fin 6) : ‖u i‖ = 1 := by
    have h := hu i
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (u i)]
  intro j
  have hDifference : (H0ᴴ *ᵥ u) j - (Hᴴ *ᵥ u) j =
      ∑ i, star (H0 i j - H i j) * u i := by
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      star_sub, sub_mul, Finset.sum_sub_distrib]
  have hDisplacement : ‖(H0ᴴ *ᵥ u) j - (Hᴴ *ᵥ u) j‖ ≤ 6 * delta := by
    rw [hDifference]
    calc
      ‖∑ i, star (H0 i j - H i j) * u i‖ ≤
          ∑ i, ‖star (H0 i j - H i j) * u i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 6, delta := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_mul, norm_star, huNorm i, mul_one] using hnear i j
      _ = 6 * delta := by simp
  have h := normSq_change_of_reference_normSq_six
    ((H0ᴴ *ᵥ u) j) ((Hᴴ *ᵥ u) j) (6 * delta)
    (mul_nonneg (by norm_num) hdelta) (hroot j) hDisplacement
  nlinarith

#print axioms common_unbiased_root_has_small_base_residual

end D5.S3.Quantum.Tomography.HadamardResidualBarrier
