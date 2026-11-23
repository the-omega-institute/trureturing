/- GID: D5/S3/Fourier/Concentration/PerturbedHarmonicWeights
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/PerturbedHarmonicWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An explicit harmonic-weight majorant on each permitted perturbation interval. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/-! Weight envelopes for comparing collision tests before and after spectral perturbations. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Fourier.Concentration.PerturbedHarmonicWeights

private theorem harmonicWeight_perturbed_le {a x y r : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hrx : r < x) (hnear : |y - x| ≤ r) :
    y / (a + y ^ 2) ≤ (x / (x - r)) * (x / (a + x ^ 2)) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hnear
  have ht : 0 < x - r := sub_pos.mpr hrx
  have hx : 0 < x := hr.trans_lt hrx
  have hy : 0 < y := by linarith
  have hlow : y * (x - r) ≤ y ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left (show x - r ≤ y by linarith) hy.le
  have hhigh : y * (x - r) ≤ x ^ 2 := by
    calc
      _ ≤ (x + r) * (x - r) :=
        mul_le_mul_of_nonneg_right (show y ≤ x + r by linarith) ht.le
      _ = x ^ 2 - r ^ 2 := by ring
      _ ≤ x ^ 2 := sub_le_self _ (sq_nonneg _)
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    _ = a * (y * (x - r)) + x ^ 2 * (y * (x - r)) := by ring
    _ ≤ a * x ^ 2 + x ^ 2 * y ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hhigh ha)
        (mul_le_mul_of_nonneg_left hlow (sq_nonneg _))
    _ = _ := by ring

end D5.S3.Fourier.Concentration.PerturbedHarmonicWeights
