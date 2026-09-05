/- GID: D5/S3/TotalVariation/SpectralSharpnessNegentropyBudget
   generality: G
   mirror-B: D5/B/S3/TotalVariation/SpectralSharpnessNegentropyBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Spectral sharpness is bounded by total variation from uniform and hence by negentropy. -/

/- Six-route duplicate and library-search audit (2026-09-04):
   * Keyword and notation searches covered `spectralSharpness`, `spectral_sharpness`, `muStar`,
     `mu_star`, `sharpness.*totalVariation`, and both orders of `sharpness` with `entropy`.
   * The frozen repository has the two separate endpoints
     `SpectralSharpness.spectralSharpness` and
     `NegentropyBudget.total_variation_uniform_le_sqrt_entropy_deficit`, but no bridge between
     them. The former is also the attained variational sharpness by
     `SpectralSharpnessDuality.spectral_sharpness_isGreatest_bounded_pairing`.
   * The current accepted-event index and digestion backfill were searched by declaration name,
     concept variants, and source atom hash. The retired legacy formalization-receipt path has no
     current counterpart to inspect. The source atom remains `residual-open` and explicitly lists
     the missing left total-variation bound.
   * Generalized searches for a reversal distance bounded by distance from a fixed point found the
     scalar triangle inequality and `Equiv.sum_comp`, but no packaged theorem matching this finite
     functional. Those Mathlib lemmas are used below instead of being reproved.
   * `origin/dev..origin/lane/math/*` had no in-flight commits when checked.
   * The uniform spectrum below is an equality witness for both inequalities, so the estimate is
     not recorded as a one-sided statement without a saturation case.
-/

import D5.S3.Entropy.EntropyEquality
import D5.S3.Quantum.Sharpness.SpectralSharpness
import D5.S3.TotalVariation.NegentropyBudget

namespace D5.S3.TotalVariation.SpectralSharpnessNegentropyBudget

open D5.S3.Entropy.EntropyEquality
open D5.S3.Entropy.MaxEntropy
open D5.S3.Quantum.Sharpness.SpectralSharpness
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.NegentropyBudget
open D5.S3.TotalVariation.Pinsker

/-- For a finite probability spectrum, spectral sharpness is at most twice its total variation
from the uniform spectrum and therefore at most the square root of twice its Shannon entropy
deficit. The uniform spectrum makes both inequalities equalities. -/
theorem spectral_sharpness_negentropy_budget
    {n : ℕ} [Nonempty (Fin n)]
    (r : Fin n → ℝ) (hr : (∀ i, 0 ≤ r i) ∧ ∑ i, r i = 1) :
    let u : Fin n → ℝ := fun _ ↦ (Fintype.card (Fin n) : ℝ)⁻¹
    spectralSharpness r ≤ 2 * totalVariation r u ∧
      2 * totalVariation r u ≤
        Real.sqrt (2 * (Real.log (Fintype.card (Fin n)) - shannonEntropy r)) ∧
      spectralSharpness u = 2 * totalVariation u u ∧
      2 * totalVariation u u =
        Real.sqrt (2 * (Real.log (Fintype.card (Fin n)) - shannonEntropy u)) := by
  classical
  let u : Fin n → ℝ := fun _ ↦ (Fintype.card (Fin n) : ℝ)⁻¹
  have hsharpness : spectralSharpness r ≤ 2 * totalVariation r u := by
    have hrev :
        (∑ i, |r (Fin.rev i) - u i|) = ∑ i, |r i - u i| := by
      simpa [u] using
        (Equiv.sum_comp Fin.revPerm (fun i : Fin n ↦ |r i - u i|))
    have hsum :
        (∑ i, |r i - r (Fin.rev i)|) ≤
          ∑ i, (|r i - u i| + |r (Fin.rev i) - u i|) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |r i - r (Fin.rev i)| = |(r i - u i) + (u i - r (Fin.rev i))| := by ring_nf
        _ ≤ |r i - u i| + |u i - r (Fin.rev i)| := abs_add_le _ _
        _ = |r i - u i| + |r (Fin.rev i) - u i| := by
          rw [abs_sub_comm (u i) (r (Fin.rev i))]
    rw [spectralSharpness, totalVariation]
    calc
      (1 / 2 : ℝ) * ∑ i, |r i - r (Fin.rev i)| ≤
          (1 / 2 : ℝ) * ∑ i, (|r i - u i| + |r (Fin.rev i) - u i|) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 2 * ((1 / 2 : ℝ) * ∑ i, |r i - u i|) := by
        rw [Finset.sum_add_distrib, hrev]
        ring
  have hnegentropy :
      2 * totalVariation r u ≤
        Real.sqrt (2 * (Real.log (Fintype.card (Fin n)) - shannonEntropy r)) := by
    exact total_variation_uniform_le_sqrt_entropy_deficit r hr
  have hcard_pos : (0 : ℝ) < Fintype.card (Fin n) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hu : (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 := by
    constructor
    · intro i
      exact (inv_pos.mpr hcard_pos).le
    · simp only [u, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      exact mul_inv_cancel₀ (by simpa using hcard_ne)
  have hu_entropy : shannonEntropy u = Real.log (Fintype.card (Fin n)) :=
    (entropy_eq_log_card_iff_uniform u hu).2 rfl
  have hu_sharpness : spectralSharpness u = 0 := by
    simp [spectralSharpness, u]
  have hu_variation : totalVariation u u = 0 := by
    simp [totalVariation]
  dsimp only
  refine ⟨hsharpness, hnegentropy, ?_, ?_⟩
  · rw [hu_sharpness, hu_variation]
    norm_num
  · rw [hu_variation, hu_entropy]
    norm_num

#print axioms spectral_sharpness_negentropy_budget

end D5.S3.TotalVariation.SpectralSharpnessNegentropyBudget
