/- GID: D5/S3/Quantum/Recovery/FourPathNearestRayComparison
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathNearestRayComparison
   mirror-E: none(waiver:nearest-ray-comparison)
   anchors: []
   utility: none
   digest: A finite-family squared-error comparison aggregates a two-term Hilbert--Schmidt decomposition.
 -/

import D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Finite-family aggregation for the nearest-ray Kraus comparison. -/

noncomputable section

open scoped BigOperators Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Recovery.FourPathNearestRayComparison

abbrev Index := Fin 4

private lemma norm_add_sq_le (x y : Matrix Index Index ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
  have hsq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
  calc
    ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := hsq
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- A finite family of two-term Hilbert--Schmidt errors satisfies the summed
quadratic estimate used in the nearest-ray Kraus comparison. -/
theorem finite_family_error_aggregation
    {J : Type*} [Fintype J]
    (K B E F : J → Matrix Index Index ℂ)
    (τ dSq : J → ℝ) (c : ℝ)
    (hdecomp : ∀ j, K j - B j = E j + F j)
    (hE : ∀ j, ‖E j‖ ^ 2 ≤ 2 * τ j)
    (hF : ∀ j, ‖F j‖ ^ 2 ≤ c * dSq j) :
    ∑ j, ‖K j - B j‖ ^ 2 ≤
      4 * (∑ j, τ j) + 2 * c * (∑ j, dSq j) := by
  have hpoint : ∀ j, ‖K j - B j‖ ^ 2 ≤ 4 * τ j + 2 * c * dSq j := by
    intro j
    rw [hdecomp j]
    calc
      ‖E j + F j‖ ^ 2 ≤ 2 * ‖E j‖ ^ 2 + 2 * ‖F j‖ ^ 2 :=
        norm_add_sq_le (E j) (F j)
      _ ≤ 4 * τ j + 2 * c * dSq j := by
        nlinarith [hE j, hF j]
  calc
    ∑ j, ‖K j - B j‖ ^ 2 ≤ ∑ j, (4 * τ j + 2 * c * dSq j) := by
      exact Finset.sum_le_sum (fun j _ => hpoint j)
    _ = 4 * (∑ j, τ j) + 2 * c * (∑ j, dSq j) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The selected larger-coordinate masses have the complementary defect given by
the sum of the coordinatewise smaller masses. -/
theorem selected_mass_bounds_and_defect
    {J : Type*} [Fintype J]
    (p q : J → ℝ) (σ : J → Bool)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j)
    (hsumP : ∑ j, p j = 1) (hsumQ : ∑ j, q j = 1)
    (hsel : ∀ j, (σ j = true ∧ q j ≤ p j) ∨ (σ j = false ∧ p j < q j)) :
    0 ≤ (∑ j, if σ j = true then p j else 0) ∧
      (∑ j, if σ j = true then p j else 0) ≤ 1 ∧
      0 ≤ (∑ j, if σ j = true then 0 else q j) ∧
      (∑ j, if σ j = true then 0 else q j) ≤ 1 ∧
      (1 - (∑ j, if σ j = true then p j else 0)) +
          (1 - (∑ j, if σ j = true then 0 else q j)) =
        (∑ j, min (p j) (q j)) := by
  have hplus_nonneg : 0 ≤ ∑ j, if σ j = true then p j else 0 := by
    exact Finset.sum_nonneg (fun j _ => by
      by_cases hs : σ j = true <;> simp [hs, hp j])
  have hplus_le : (∑ j, if σ j = true then p j else 0) ≤ ∑ j, p j := by
    exact Finset.sum_le_sum (fun j _ => by
      by_cases hs : σ j = true <;> simp [hs, hp j])
  have hminus_nonneg : 0 ≤ ∑ j, if σ j = true then 0 else q j := by
    exact Finset.sum_nonneg (fun j _ => by
      by_cases hs : σ j = true <;> simp [hs, hq j])
  have hminus_le : (∑ j, if σ j = true then 0 else q j) ≤ ∑ j, q j := by
    exact Finset.sum_le_sum (fun j _ => by
      by_cases hs : σ j = true <;> simp [hs, hq j])
  have hpoint : ∀ j,
      (p j - (if σ j = true then p j else 0)) +
          (q j - (if σ j = true then 0 else q j)) = min (p j) (q j) := by
    intro j
    rcases hsel j with ⟨hs, hqp⟩ | ⟨hs, hpq⟩
    · simp [hs, min_eq_right hqp]
    · simp [hs, min_eq_left hpq.le]
  refine ⟨hplus_nonneg, hplus_le.trans_eq hsumP, hminus_nonneg,
    hminus_le.trans_eq hsumQ, ?_⟩
  calc
    (1 - ∑ j, if σ j = true then p j else 0) +
        (1 - ∑ j, if σ j = true then 0 else q j) =
        ((∑ j, p j) - ∑ j, if σ j = true then p j else 0) +
          ((∑ j, q j) - ∑ j, if σ j = true then 0 else q j) := by
            rw [hsumP, hsumQ]
    _ = ∑ j, ((p j - (if σ j = true then p j else 0)) +
          (q j - (if σ j = true then 0 else q j))) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib]
    _ = ∑ j, min (p j) (q j) := by
      exact Finset.sum_congr rfl (fun j _ => hpoint j)

end D5.S3.Quantum.Recovery.FourPathNearestRayComparison
