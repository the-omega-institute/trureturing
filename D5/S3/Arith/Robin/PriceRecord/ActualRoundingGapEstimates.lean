import D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Tactic

/-! Finite estimates for the exact integer gap at positive price, including
its logarithmic identity and majorant in the chamber with candidates 1 and 2. -/

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates

open Real Set
open BoundaryPrimePrice
open QuantitativePrimeAbel (log_deficit_bounds)

private lemma benefit_mono {p s t : ℝ} (hp : 1 < p)
    (hs : 1 ≤ s) (hst : s ≤ t) : benefit p s ≤ benefit p t := by
  have ht := hs.trans hst
  have hus := probability_mem hp hs
  have hut := probability_mem hp ht
  have hpow : probability p t ≤ probability p s := by
    exact rpow_le_rpow_of_exponent_le hp.le (by linarith)
  rw [benefit_log hp hs, benefit_log hp ht]
  exact sub_le_sub_right (log_le_log (by linarith) (by linarith)) _

private lemma benefit_saturation {p t : ℝ} (hp : 1 < p) (ht : 1 ≤ t) :
    benefit p t ≤ -log (1 - p ^ (-1 : ℝ)) := by
  have hu := probability_mem hp ht
  rw [benefit_log hp ht]
  have hlog : log (1 - probability p t) ≤ 0 :=
    log_nonpos (by linarith) (by linarith)
  linarith

/-- Both all-prime envelopes hold for the actual floor/ceiling minimum,
including inactive primes and coincident floor/ceiling candidates. -/
theorem integer_gap_global_bounds {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam) :
    0 ≤ integerGap p lam ∧
      integerGap p lam ≤ lam * log p ∧
      integerGap p lam ≤ -log (1 - (p ^ (2 : ℕ))⁻¹) := by
  have hb : 1 ≤ boundary p lam := le_max_left _ _
  have hc : (1 : ℤ) ≤ ⌈boundary p lam⌉ := by
    exact_mod_cast (hb.trans (Int.le_ceil (boundary p lam)))
  have hcR : (1 : ℝ) ≤ (⌈boundary p lam⌉ : ℤ) := by exact_mod_cast hc
  have hnonneg := (integer_gap_bounds hp hlam (1 : ℤ) (by norm_num)).1
  refine ⟨hnonneg, ?_, ?_⟩
  · have hi := (integer_gap_bounds hp hlam ⌈boundary p lam⌉ hc).2
    have hbenefit := benefit_mono hp hb (Int.le_ceil (boundary p lam))
    have hdist : ((⌈boundary p lam⌉ : ℤ) : ℝ) - boundary p lam ≤ 1 := by
      linarith [Int.ceil_lt_add_one (boundary p lam)]
    have hcost := mul_le_mul_of_nonneg_right hdist
      (mul_nonneg hlam.le (log_pos hp).le)
    dsimp only [priceLoss, priceObjective] at hi
    nlinarith
  · have hi := (integer_gap_bounds hp hlam (1 : ℤ) (by norm_num)).2
    have hsat := benefit_saturation hp hb
    have hcost : 0 ≤ lam * (boundary p lam - 1) * log p :=
      mul_nonneg (mul_nonneg hlam.le (sub_nonneg.mpr hb)) (log_pos hp).le
    have hprob : probability p 1 = (p ^ (2 : ℕ))⁻¹ := by
      dsimp [probability]
      norm_num only [one_add_one_eq_two]
      rw [rpow_neg (by linarith : 0 ≤ p), rpow_two]
    have hone := benefit_log hp (le_refl (1 : ℝ))
    rw [hprob] at hone
    norm_num only [Int.cast_one] at hi
    dsimp only [priceLoss, priceObjective] at hi
    linarith

private lemma chamber_critical {p lam : ℝ} (hp : 1 < p)
    (hlo : p ^ (2 : ℕ) < cutoff lam) (hhi : cutoff lam < p ^ (3 : ℕ)) :
    1 < critical p lam ∧ critical p lam < 2 := by
  have hp0 : 0 < p := by linarith
  have hC0 : 0 < cutoff lam := lt_trans (pow_pos hp0 _) hlo
  have hq := log_pos hp
  have hl := (log_lt_log_iff (pow_pos hp0 2) hC0).mpr hlo
  have hu := (log_lt_log_iff hC0 (pow_pos hp0 3)).mpr hhi
  rw [log_pow] at hl hu
  norm_num only [Nat.cast_ofNat] at hl hu
  have hl' : 2 < log (cutoff lam) / log p :=
    (lt_div_iff₀ hq).mpr (by nlinarith)
  have hu' : log (cutoff lam) / log p < 3 :=
    (div_lt_iff₀ hq).mpr (by nlinarith)
  dsimp [critical]
  constructor <;> linarith

/-- An exact nonlinear formula in the open two-integer chamber.
The common correction is retained, including the literal cutoff 1+lam^-1.
This formula does not select which of 1 and 2 wins. -/
theorem integer_gap_chamber_identity {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hlo : p ^ (2 : ℕ) < cutoff lam) (hhi : cutoff lam < p ^ (3 : ℕ)) :
    integerGap p lam =
      min (-log (1 - (p ^ (2 : ℕ))⁻¹))
        (-log (1 - (p ^ (3 : ℕ))⁻¹) + lam * log p) -
      (-log (1 - (cutoff lam)⁻¹) + lam * log (cutoff lam / p ^ (2 : ℕ))) := by
  have hp0 : 0 < p := by linarith
  have hc := chamber_critical hp hlo hhi
  have hb : boundary p lam = critical p lam := max_eq_right hc.1.le
  have hf : ⌊critical p lam⌋ = (1 : ℤ) :=
    Int.floor_eq_iff.mpr (by norm_num; exact ⟨hc.1.le, hc.2⟩)
  have he : ⌈critical p lam⌉ = (2 : ℤ) :=
    Int.ceil_eq_iff.mpr (by norm_num; exact ⟨hc.1, hc.2.le⟩)
  have hu2 := probability_mem hp (le_refl (1 : ℝ))
  have hu3 := probability_mem hp (by norm_num : (1 : ℝ) ≤ 2)
  have hprob2 : probability p 1 = (p ^ (2 : ℕ))⁻¹ := by
    dsimp [probability]
    norm_num only [one_add_one_eq_two]
    rw [rpow_neg hp0.le, rpow_two]
  have hprob3 : probability p 2 = (p ^ (3 : ℕ))⁻¹ := by
    dsimp [probability]
    norm_num only [show (2 : ℝ) + 1 = 3 by norm_num]
    rw [rpow_neg hp0.le, rpow_ofNat]
  rw [hprob2] at hu2
  rw [hprob3] at hu3
  have hC : 1 < cutoff lam := by
    dsimp [cutoff]
    linarith [inv_pos.mpr hlam]
  have hC0 : 0 < cutoff lam := by linarith
  have hr : (cutoff lam)⁻¹ < 1 := (inv_lt_one₀ hC0).mpr hC
  have h1 := (active_loss hp hlam hlo (le_refl (1 : ℝ))).2
  have h2 := (active_loss hp hlam hlo (by norm_num : (1 : ℝ) ≤ 2)).2
  rw [hprob2] at h1
  rw [hprob3] at h2
  norm_num only [one_add_one_eq_two, rpow_two] at h1
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num] at h2
  rw [rpow_ofNat] at h2
  rw [log_div (by linarith : 1 - (cutoff lam)⁻¹ ≠ 0)
    (by linarith : 1 - (p ^ (2 : ℕ))⁻¹ ≠ 0)] at h1
  rw [log_div (by linarith : 1 - (cutoff lam)⁻¹ ≠ 0)
    (by linarith : 1 - (p ^ (3 : ℕ))⁻¹ ≠ 0)] at h2
  have hlog : log (cutoff lam / p ^ (3 : ℕ)) =
      log (cutoff lam / p ^ (2 : ℕ)) - log p := by
    rw [log_div hC0.ne' (pow_pos hp0 3).ne',
      log_div hC0.ne' (pow_pos hp0 2).ne', log_pow, log_pow]
    ring
  rw [hlog] at h2
  rw [integerGap, hb, hf, he]
  norm_num only [Int.cast_one, Int.cast_ofNat]
  rw [h1, h2]
  rcases le_total (-log (1 - (p ^ (2 : ℕ))⁻¹))
      (-log (1 - (p ^ (3 : ℕ))⁻¹) + lam * log p) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, min_eq_right (by linarith)]
    ring

/-- A finite explicit estimate; its hypotheses are just the genuine
two-integer chamber. No asymptotic convergence is assumed. -/
theorem integer_gap_chamber_error {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hlo : p ^ (2 : ℕ) < cutoff lam) (hhi : cutoff lam < p ^ (3 : ℕ)) :
    |integerGap p lam - min ((p ^ (2 : ℕ))⁻¹) (lam * log p)| ≤
      (cutoff lam)⁻¹ / (1 - (cutoff lam)⁻¹) +
        lam * log (cutoff lam / p ^ (2 : ℕ)) +
        ((p ^ (2 : ℕ))⁻¹) ^ 2 / (1 - (p ^ (2 : ℕ))⁻¹) +
        (p ^ (3 : ℕ))⁻¹ / (1 - (p ^ (3 : ℕ))⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 1 < p ^ (2 : ℕ) := one_lt_pow₀ hp (by norm_num)
  have hp3 : 1 < p ^ (3 : ℕ) := one_lt_pow₀ hp (by norm_num)
  have hC : 1 < cutoff lam := lt_trans hp2 hlo
  have hC0 : 0 < cutoff lam := by linarith
  let u : ℝ := (p ^ (2 : ℕ))⁻¹
  let v : ℝ := (p ^ (3 : ℕ))⁻¹
  let r : ℝ := (cutoff lam)⁻¹
  have hu0 : 0 < u := inv_pos.mpr (pow_pos hp0 _)
  have hv0 : 0 < v := inv_pos.mpr (pow_pos hp0 _)
  have hr0 : 0 < r := inv_pos.mpr hC0
  have hu1 : u < 1 := (inv_lt_one₀ (pow_pos hp0 _)).mpr hp2
  have hv1 : v < 1 := (inv_lt_one₀ (pow_pos hp0 _)).mpr hp3
  have hr1 : r < 1 := (inv_lt_one₀ hC0).mpr hC
  have hbu := log_deficit_bounds hu0.le hu1
  have hbv := log_deficit_bounds hv0.le hv1
  have hbr := log_deficit_bounds hr0.le hr1
  have hlog0 : 0 ≤ log (cutoff lam / p ^ (2 : ℕ)) :=
    log_nonneg ((one_le_div (pow_pos hp0 _)).mpr hlo.le)
  have huerr : u / (1 - u) = u + u ^ 2 / (1 - u) := by
    field_simp [show 1 - u ≠ 0 by linarith]
    <;> ring
  have hminlo : min u (lam * log p) ≤
      min (-log (1 - u)) (-log (1 - v) + lam * log p) :=
    min_le_min hbu.1 (by linarith [hbv.1])
  have hminhi : min (-log (1 - u)) (-log (1 - v) + lam * log p) ≤
      min u (lam * log p) + u ^ 2 / (1 - u) + v / (1 - v) := by
    have hE : 0 ≤ u ^ 2 / (1 - u) := by positivity
    have hF : 0 ≤ v / (1 - v) := by positivity
    rcases le_total u (lam * log p) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by rw [huerr] at hbu; linarith [hbu.2])
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith [hbv.2])
  have hid := integer_gap_chamber_identity hp hlam hlo hhi
  change integerGap p lam =
    min (-log (1 - u)) (-log (1 - v) + lam * log p) -
      (-log (1 - r) + lam * log (cutoff lam / p ^ (2 : ℕ))) at hid
  change |integerGap p lam - min u (lam * log p)| ≤ _
  rw [hid]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hlam.le hlog0,
    div_nonneg (sq_nonneg u) (by linarith : 0 ≤ 1 - u),
    div_nonneg hv0.le (by linarith : 0 ≤ 1 - v)]

end D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
