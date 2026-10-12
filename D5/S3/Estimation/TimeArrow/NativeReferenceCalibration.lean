/- GID: D5/S3/Estimation/TimeArrow/NativeReferenceCalibration
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeReferenceCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact compensated reference calibration retains both complete row populations. -/

import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open private
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
from D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
noncomputable section

/-- Complete count-level calibration at zero common odds shift. -/
def referenceParameter (M q : ℕ) (r : ℝ) (c : ℕ × ℕ) : ℝ :=
  Real.sigmoid (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
    c.2 * Real.log ((1 - r) / (1 + compensation M q r)) -
    Real.log (((M - q : ℕ) : ℝ) / q))

private theorem reference_factor {M q : ℕ} (S : Support M q) (r : ℝ) (L : ℕ)
    (i : Fin M) (c : ℕ × ℕ) :
    rowReference S r L i c = Real.exp (-(L : ℝ)) *
      (((L : ℝ) * (1 + b r S (.inl i)) / 2) ^ c.1 *
        ((L : ℝ) * (1 - b r S (.inl i)) / 2) ^ c.2) /
          (c.1.factorial * c.2.factorial : ℕ) := by
  unfold rowReference
  push_cast
  have hexp : Real.exp (-((L : ℝ) * (1 + b r S (.inl i)) / 2)) *
      Real.exp (-((L : ℝ) * (1 - b r S (.inl i)) / 2)) = Real.exp (-(L : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-((L : ℝ) * (1 + b r S (.inl i)) / 2)) *
        Real.exp (-((L : ℝ) * (1 - b r S (.inl i)) / 2))) *
      (((L : ℝ) * (1 + b r S (.inl i)) / 2) ^ c.1 *
        ((L : ℝ) * (1 - b r S (.inl i)) / 2) ^ c.2) /
          ((c.1.factorial : ℝ) * c.2.factorial) := by ring
    _ = _ := by rw [hexp]

theorem reference_likelihood_ratio {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) (c : ℕ × ℕ) :
    rowReference S r L i c =
      Real.exp (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
        c.2 * Real.log ((1 - r) / (1 + compensation M q r))) * rowReference S r L j c := by
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have hp : 0 < (1 + r) / (1 - compensation M q r) := div_pos (by linarith) (by linarith)
  have hm : 0 < (1 - r) / (1 + compensation M q r) := div_pos (by linarith) (by linarith)
  have hexp : Real.exp (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r))) =
      ((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2 := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hp, Real.exp_log hm]
  rw [hexp, reference_factor, reference_factor]
  simp only [b, if_pos hi, if_neg hj, sub_neg_eq_add]
  have hplus : ((1 + r) / (1 - compensation M q r)) *
      ((L : ℝ) * (1 + -compensation M q r) / 2) = (L : ℝ) * (1 + r) / 2 := by
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    <;> ring
  have hminus : ((1 - r) / (1 + compensation M q r)) *
      ((L : ℝ) * (1 + compensation M q r) / 2) = (L : ℝ) * (1 - r) / 2 := by
    field_simp
    <;> ring
  have he :
      (((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2) *
      (((L : ℝ) * (1 + -compensation M q r) / 2) ^ c.1 *
        ((L : ℝ) * (1 + compensation M q r) / 2) ^ c.2) =
      ((L : ℝ) * (1 + r) / 2) ^ c.1 * ((L : ℝ) * (1 - r) / 2) ^ c.2 := by
    rw [show ∀ a b d e : ℝ, (a * b) * (d * e) = (a * d) * (b * e) by intros; ring,
      ← mul_pow, ← mul_pow, hplus, hminus]
  calc
    _ = Real.exp (-(L : ℝ)) *
      ((((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2) *
      (((L : ℝ) * (1 + -compensation M q r) / 2) ^ c.1 *
        ((L : ℝ) * (1 + compensation M q r) / 2) ^ c.2)) /
        (c.1.factorial * c.2.factorial : ℕ) := by rw [he]
    _ = _ := by ring

private theorem pointwise_calibration {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) (c : ℕ × ℕ) :
    ((q : ℝ) * rowReference S r L i c + ((M - q : ℕ) : ℝ) * rowReference S r L j c) *
      referenceParameter M q r c = (q : ℝ) * rowReference S r L i c := by
  let W := c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r))
  let B : ℝ := ((M - q : ℕ) : ℝ) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN : (0 : ℝ) < (M - q : ℕ) := by exact_mod_cast (show 0 < M - q by omega)
  have hB : 0 < B := div_pos hN hqR
  have hR : rowReference S r L i c = Real.exp W * rowReference S r L j c :=
    reference_likelihood_ratio S r κ hκ hr hrκ hcκ hL i j hi hj c
  rw [hR]
  change _ * Real.sigmoid (W - Real.log B) = _
  rw [Real.sigmoid_def, neg_sub, Real.exp_sub, Real.exp_log hB]
  dsimp [B]
  field_simp
  <;> ring

/-- The complete reference mean is exactly q. Its complete calibration
variance is the signal reference expectation of one minus the same parameter. -/
theorem reference_calibration_mean_variance {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) :
    ((q : ℝ) * (∑' c, referenceParameter M q r c * rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, referenceParameter M q r c * rowReference S r L j c) = q) ∧
    ((q : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L j c) =
      (q : ℝ) * (∑' c, (1 - referenceParameter M q r c) * rowReference S r L i c)) := by
  let p := referenceParameter M q r
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 :=
    ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ p c * (1 - p c) ∧ p c * (1 - p c) ≤ 1 := by
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hs (g : ℕ × ℕ → ℝ) (hg : ∀ c, 0 ≤ g c ∧ g c ≤ 1) (k : Fin M) :
      Summable (fun c => g c * rowReference S r L k c) :=
    (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
      S r κ hκ hr hrκ hcκ hL k g hg).1
  have hpoint := pointwise_calibration S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hnorm : (∑' c, rowReference S r L i c) = 1 := by
    have hh := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
      S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
    simpa using hh.tsum_eq
  constructor
  · have hadd := ((hs p hp i).mul_left (q : ℝ)).tsum_add
      ((hs p hp j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * (p c * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * (p c * rowReference S r L j c) =
        (q : ℝ) * rowReference S r L i c := by
      have hh := hpoint c
      change (_ * p c) = _ at hh
      nlinarith
    simp_rw [he]
    rw [tsum_mul_left, hnorm, mul_one]
  · have hadd := ((hs (fun c => p c * (1 - p c)) hv i).mul_left (q : ℝ)).tsum_add
      ((hs (fun c => p c * (1 - p c)) hv j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * ((p c * (1 - p c)) * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * ((p c * (1 - p c)) * rowReference S r L j c) =
        (q : ℝ) * ((1 - p c) * rowReference S r L i c) := by
      have hh := congrArg (fun x : ℝ => x * (1 - p c)) (hpoint c)
      change _ = _ at hh
      nlinarith
    simp_rw [he]
    rw [tsum_mul_left]

private theorem all_row_reference_sum {M q L : ℕ} (S : Support M q) (r : ℝ)
    (g : ℕ × ℕ → ℝ) (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) :
    (∑ k : Fin M, ∑' c, g c * rowReference S r L k c) =
      (q : ℝ) * (∑' c, g c * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * (∑' c, g c * rowReference S r L j c) := by
  classical
  have hk (k : Fin M) : (∑' c, g c * rowReference S r L k c) =
      if k ∈ S.val then (∑' c, g c * rowReference S r L i c)
      else (∑' c, g c * rowReference S r L j c) := by
    by_cases h : k ∈ S.val
    · rw [if_pos h]
      congr 1
      funext c
      simp only [rowReference, b, if_pos h, if_pos hi]
    · rw [if_neg h]
      congr 1
      funext c
      simp only [rowReference, b, if_neg h, if_neg hj]
  rw [sum_congr rfl (fun k _ => hk k)]
  rw [sum_ite]
  have hsig : (univ.filter fun k : Fin M => k ∈ S.val) = S.val := by ext k; simp
  have hbg : (univ.filter fun k : Fin M => k ∉ S.val).card = M - q := by
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (p := fun k => k ∈ S.val)
    rw [hsig, S.property] at hc
    simp only [card_univ, Fintype.card_fin] at hc
    omega
  simp [hsig, hbg, S.property]

/-- The reference calibration identities control all-row mean and variance
deviations under each original law, with a common restored-tail budget. -/
theorem native_reference_calibration_deviation (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ b h : ℝ, 0 < b → 0 < h →
          let p := referenceParameter M q r
          let V := ∑ k : Fin M, ∑' c, (p c * (1 - p c)) * rowReference S r L k c
          let P := fun o : Obs M (2 * M * L) e =>
            ∑ k : Fin M, p (count e o k 1, count e o k (-1))
          let D := fun o : Obs M (2 * M * L) e =>
            ∑ k : Fin M, p (count e o k 1, count e o k (-1)) *
              (1 - p (count e o k 1, count e o k (-1)))
          let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
            10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          0 ≤ V ∧ V ≤ q ∧
            (∑ o, if b < |P o - q| ∨ h < |D o - V| then probability r e S o else 0) ≤
              B / b ^ 2 + B / h ^ 2 := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_full_weighted_deviation κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e i j hi hj b t hb ht
  let p := referenceParameter M q r
  let v := fun c : ℕ × ℕ => p c * (1 - p c)
  let V := ∑ k : Fin M, ∑' c, v c * rowReference S r L k c
  let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
      10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 :=
    ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ v c ∧ v c ≤ 1 := by
    dsimp [v]
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith only [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hcal := reference_calibration_mean_variance S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hmean : (∑ k : Fin M, ∑' c, p c * rowReference S r L k c) = (q : ℝ) := by
    rw [all_row_reference_sum S r p i j hi hj]
    exact hcal.1
  have hVar : V = (q : ℝ) * (∑' c, (1 - p c) * rowReference S r L i c) := by
    dsimp [V]
    rw [all_row_reference_sum S r v i j hi hj]
    exact hcal.2
  have hQ (c : ℕ × ℕ) : 0 ≤ rowReference S r L i c :=
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hcomplement (c : ℕ × ℕ) : 0 ≤ 1 - p c ∧ 1 - p c ≤ 1 := by
    constructor <;> linarith [(hp c).1, (hp c).2]
  have hs := (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
    S r κ hκ hr hrκ hcκ hL i (fun c => 1 - p c) hcomplement).1
  have hnorm := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
    S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
  have htotal : (∑' c, rowReference S r L i c) = 1 := by simpa using hnorm.tsum_eq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hV0 : 0 ≤ V := by
    rw [hVar]
    exact mul_nonneg hq0 (tsum_nonneg fun c => mul_nonneg (hcomplement c).1 (hQ c))
  have hVq : V ≤ q := by
    rw [hVar]
    have hh := hs.tsum_le_tsum (fun c => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcomplement c).2 (hQ c))
      (by simpa only [one_pow, one_mul] using hnorm.summable)
    rw [htotal] at hh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hq0
  have hP := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ
    (fun _ => p) (fun _ c => hp c) b hb
  simp only [hmean, card_univ, Fintype.card_fin] at hP
  have hD := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ
    (fun _ => v) (fun _ c => hv c) t ht
  have hδ : 0 ≤ A * (L : ℝ) ^ 3 / M := by positivity
  have hbudget : 3 * V + 8 * (A * (L : ℝ) ^ 3 / M) * V ^ 2 +
      10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) ≤ B := by
    have hsq : V ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith only [hV0, hVq, hq0]
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8 * (A * (L : ℝ) ^ 3 / M) by positivity)
    dsimp [B]
    linarith only [hVq, hh]
  have hD' : (∑ o : Obs M (2 * M * L) e,
      if t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0) ≤ B / t ^ 2 := by
    apply hD.trans
    simp only [card_univ, Fintype.card_fin]
    exact div_le_div_of_nonneg_right hbudget (sq_nonneg t)
  refine ⟨hV0, hVq, ?_⟩
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have hprob := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S
  apply le_trans _ (add_le_add hP hD')
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro o _
  change (if b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q| ∨
      t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0) ≤
    (if b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q|
      then probability r e S o else 0) +
    (if t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0)
  by_cases hp' : b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q| <;>
    by_cases hd' : t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V| <;>
    simp only [hp', hd', or_true, true_or, or_false, false_or, if_true, if_false]
  · exact le_add_of_nonneg_right (hprob o)
  · simp
  · simp
  · simp

end
end D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
