/- GID: D5/S3/Weil/Scattering/VerticalAttenuation
   generality: G
   mirror-B: D5/B/S3/Weil/Scattering/VerticalAttenuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite Blaschke logarithmic profile equals the sum of one-factor vertical attenuations. -/

import Mathlib

namespace D5.S3.Weil.Scattering.VerticalAttenuation

open MeasureTheory

theorem vertical_attenuation_tomography
    {ι : Type*} [Fintype ι]
    (A : ℝ → ℝ) (profile : ℝ → ℝ → ℝ) (factor : ι → ℝ → ℝ → ℝ)
    (realPart : ι → ℝ)
    (hA : ∀ y, A y = (1 / (4 * Real.pi)) * ∫ x : ℝ, profile x y)
    (hdecomp : ∀ x y, profile x y = ∑ i, factor i x y)
    (hintegrable : ∀ i y, Integrable (fun x : ℝ => factor i x y))
    (hone : ∀ i y, 0 < y →
      (1 / (4 * Real.pi)) * ∫ x : ℝ, factor i x y = min y (realPart i))
    (y : ℝ) (hy : 0 < y) :
    A y = ∑ i, min y (realPart i) := by
  rw [hA, integral_congr_ae (Filter.Eventually.of_forall (fun x => hdecomp x y))]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hone i y hy
  · intro i hi
    exact hintegrable i y

end D5.S3.Weil.Scattering.VerticalAttenuation
