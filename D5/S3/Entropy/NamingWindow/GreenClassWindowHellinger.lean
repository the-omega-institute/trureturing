/- GID: D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger
   generality: G
   mirror-B: D5/B/S3/Entropy/NamingWindow/GreenClassWindowHellinger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor window affinity and bound its exact squared-Hellinger product defect. -/

/- Repository and library-search audit trail (2026-08-15):
   * `GreenClassWindowEntropy.windowLaw` supplies the finite coordinate product. Its private
     `sum_prod_update` helper was inspected, but the affinity proof needs only the more direct
     pinned-mathlib factorization `Fintype.prod_sum`, so that helper is not restated here.
   * `BhattacharyyaProduct.bhattacharyya_product_multiplicative` supplies the binary proof shape:
     regroup each radicand, apply the asymmetric square-root product law, and factor finite sums.
     The theorem itself is imported and is not restated.
   * Pinned-mathlib searches for `sqrt_prod`, `prod_sum`, `one_sub_prod`, and product bounds found
     `Real.sqrt_prod`, `Fintype.prod_sum`, `Finset.prod_nonneg`, and `Finset.prod_le_one`, but no
     finite product-defect inequality. The latter is proved below by `Finset.induction`.
-/

import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.TotalVariation.BhattacharyyaProduct
import D5.S3.TotalVariation.HellingerDivergence

namespace D5.S3.Entropy.NamingWindow.GreenClassWindowHellinger

open Finset
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.HellingerDivergence
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy

noncomputable section

/-- **Window Bhattacharyya multiplicativity.** -/
theorem bhattacharyya_windowLaw {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p q : ι → O → ℝ) (hpq : ∀ i a, 0 ≤ p i a * q i a) :
    bhattacharyya (windowLaw p) (windowLaw q) = ∏ i, bhattacharyya (p i) (q i) := by
  classical
  rw [bhattacharyya]
  calc
    (∑ u : ι → O, Real.sqrt (windowLaw p u * windowLaw q u)) =
        ∑ u : ι → O, ∏ i, Real.sqrt (p i (u i) * q i (u i)) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [windowLaw, windowLaw, ← Finset.prod_mul_distrib,
        Real.sqrt_prod Finset.univ (fun i _ => hpq i (u i))]
    _ = ∏ i, ∑ a, Real.sqrt (p i a * q i a) :=
      (Fintype.prod_sum (fun i a => Real.sqrt (p i a * q i a))).symm
    _ = ∏ i, bhattacharyya (p i) (q i) := by
      exact Finset.prod_congr rfl fun i _ => rfl

/-- **Window squared Hellinger distance is an exact product defect.** -/
theorem hellingerSq_windowLaw_product_defect
    {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p q : ι → O → ℝ)
    (hp : ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1)
    (hq : ∀ i, (∀ a, 0 ≤ q i a) ∧ ∑ a, q i a = 1) :
    hellingerSq (windowLaw p) (windowLaw q) =
      2 * (1 - ∏ i, (1 - hellingerSq (p i) (q i) / 2)) := by
  classical
  have hpw : (∀ u, 0 ≤ windowLaw p u) ∧ ∑ u, windowLaw p u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hp i).1 (u i),
      windowLaw_sum_eq_one p fun i => (hp i).2⟩
  have hqw : (∀ u, 0 ≤ windowLaw q u) ∧ ∑ u, windowLaw q u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hq i).1 (u i),
      windowLaw_sum_eq_one q fun i => (hq i).2⟩
  rw [hellinger_sq_eq_two_sub (windowLaw p) (windowLaw q) hpw hqw,
    bhattacharyya_windowLaw p q (fun i a => mul_nonneg ((hp i).1 a) ((hq i).1 a))]
  congr 2
  exact Finset.prod_congr rfl fun i _ => by
    have hi := hellinger_sq_eq_two_sub (p i) (q i) (hp i) (hq i)
    linarith

/-- **Window squared Hellinger distance is bounded by the coordinate sum.** -/
theorem hellingerSq_windowLaw_le_sum
    {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p q : ι → O → ℝ)
    (hp : ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1)
    (hq : ∀ i, (∀ a, 0 ≤ q i a) ∧ ∑ a, q i a = 1) :
    hellingerSq (windowLaw p) (windowLaw q) ≤ ∑ i, hellingerSq (p i) (q i) := by
  classical
  let x : ι → ℝ := fun i => hellingerSq (p i) (q i) / 2
  have hx_nonneg (i : ι) : 0 ≤ x i := by
    exact div_nonneg (hellinger_sq_nonneg (p i) (q i)) (by norm_num)
  have hx_le_one (i : ι) : x i ≤ 1 := by
    have hbridge := hellinger_sq_eq_two_sub (p i) (q i) (hp i) (hq i)
    have hbc : 0 ≤ bhattacharyya (p i) (q i) := by
      rw [bhattacharyya]
      exact Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _
    dsimp [x]
    linarith
  have hdefect (s : Finset ι) :
      1 - ∏ i ∈ s, (1 - x i) ≤ ∑ i ∈ s, x i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have hprod_nonneg : 0 ≤ ∏ i ∈ s, (1 - x i) :=
          Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hx_le_one i)
        have hprod_le_one : ∏ i ∈ s, (1 - x i) ≤ 1 :=
          Finset.prod_le_one
            (fun i _ => sub_nonneg.mpr (hx_le_one i))
            (fun i _ => by linarith [hx_nonneg i])
        have hmul : x a * (∏ i ∈ s, (1 - x i)) ≤ x a := by
          nlinarith [mul_le_mul_of_nonneg_left hprod_le_one (hx_nonneg a)]
        nlinarith
  rw [hellingerSq_windowLaw_product_defect p q hp hq]
  calc
    2 * (1 - ∏ i, (1 - hellingerSq (p i) (q i) / 2)) =
        2 * (1 - ∏ i, (1 - x i)) := by rfl
    _ ≤ 2 * ∑ i, x i :=
      mul_le_mul_of_nonneg_left (hdefect Finset.univ) (by norm_num)
    _ = ∑ i, hellingerSq (p i) (q i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        dsimp [x]
        ring

end

end D5.S3.Entropy.NamingWindow.GreenClassWindowHellinger
