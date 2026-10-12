/- GID: D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original full posterior and native conditional mass use one shared calibration. -/
import D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
import D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds
import D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
import Mathlib.Analysis.SpecialFunctions.Stirling
import D5.S3.DivergenceSupport.LogSumInequality
open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open private
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
from D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
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
  rw [hexp, reference_factor, reference_factor]; simp only [b, if_pos hi, if_neg hj, sub_neg_eq_add]
  have hplus : ((1 + r) / (1 - compensation M q r)) *
      ((L : ℝ) * (1 + -compensation M q r) / 2) = (L : ℝ) * (1 + r) / 2 := by
    field_simp [ne_of_gt (sub_pos.mpr hc1)] <;> ring
  have hminus : ((1 - r) / (1 + compensation M q r)) *
      ((L : ℝ) * (1 + compensation M q r) / 2) = (L : ℝ) * (1 - r) / 2 := by
    field_simp <;> ring
  have he : (((1 + r) / (1 - compensation M q r)) ^ c.1 * ((1 - r) / (1 + compensation M q r)) ^ c.2) *
      (((L : ℝ) * (1 + -compensation M q r) / 2) ^ c.1 *
        ((L : ℝ) * (1 + compensation M q r) / 2) ^ c.2) =
      ((L : ℝ) * (1 + r) / 2) ^ c.1 * ((L : ℝ) * (1 - r) / 2) ^ c.2 := by
    rw [show ∀ a b d e : ℝ, (a * b) * (d * e) = (a * d) * (b * e) by intros; ring, ← mul_pow, ← mul_pow, hplus, hminus]
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
  let W := c.1 * Real.log ((1 + r) / (1 - compensation M q r)) + c.2 * Real.log ((1 - r) / (1 + compensation M q r))
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
  field_simp <;> ring
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
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 := ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ p c * (1 - p c) ∧ p c * (1 - p c) ≤ 1 := by
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hs (g : ℕ × ℕ → ℝ) (hg : ∀ c, 0 ≤ g c ∧ g c ≤ 1) (k : Fin M) : Summable (fun c => g c * rowReference S r L k c) :=
    (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
      S r κ hκ hr hrκ hcκ hL k g hg).1
  have hpoint := pointwise_calibration S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hnorm : (∑' c, rowReference S r L i c) = 1 := by
    have hh := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
      S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
    simpa using hh.tsum_eq
  constructor
  · have hadd := ((hs p hp i).mul_left (q : ℝ)).tsum_add ((hs p hp j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * (p c * rowReference S r L i c) + ((M - q : ℕ) : ℝ) * (p c * rowReference S r L j c) =
        (q : ℝ) * rowReference S r L i c := by
      have hh := hpoint c
      change (_ * p c) = _ at hh; nlinarith
    simp_rw [he]
    rw [tsum_mul_left, hnorm, mul_one]
  · have hadd := ((hs (fun c => p c * (1 - p c)) hv i).mul_left (q : ℝ)).tsum_add
      ((hs (fun c => p c * (1 - p c)) hv j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * ((p c * (1 - p c)) * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * ((p c * (1 - p c)) * rowReference S r L j c) =
        (q : ℝ) * ((1 - p c) * rowReference S r L i c) := by
      have hh := congrArg (fun x : ℝ => x * (1 - p c)) (hpoint c)
      change _ = _ at hh; nlinarith
    simp_rw [he]
    rw [tsum_mul_left]
private theorem all_row_reference_sum {M q L : ℕ} (S : Support M q) (r : ℝ)
    (g : ℕ × ℕ → ℝ) (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) :
    (∑ k : Fin M, ∑' c, g c * rowReference S r L k c) =
      (q : ℝ) * (∑' c, g c * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * (∑' c, g c * rowReference S r L j c) := by
  classical
  have hk (k : Fin M) : (∑' c, g c * rowReference S r L k c) = if k ∈ S.val then (∑' c, g c * rowReference S r L i c)
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
    rw [hsig, S.property] at hc; simp only [card_univ, Fintype.card_fin] at hc
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
  let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 + 10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 := ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ v c ∧ v c ≤ 1 := by
    dsimp [v]
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith only [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hcal := reference_calibration_mean_variance S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hmean : (∑ k : Fin M, ∑' c, p c * rowReference S r L k c) = (q : ℝ) := by
    rw [all_row_reference_sum S r p i j hi hj]; exact hcal.1
  have hVar : V = (q : ℝ) * (∑' c, (1 - p c) * rowReference S r L i c) := by
    dsimp [V]
    rw [all_row_reference_sum S r v i j hi hj]; exact hcal.2
  have hQ (c : ℕ × ℕ) : 0 ≤ rowReference S r L i c :=
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hcomplement (c : ℕ × ℕ) : 0 ≤ 1 - p c ∧ 1 - p c ≤ 1 := by constructor <;> linarith [(hp c).1, (hp c).2]
  have hs := (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
    S r κ hκ hr hrκ hcκ hL i (fun c => 1 - p c) hcomplement).1
  have hnorm := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
    S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
  have htotal : (∑' c, rowReference S r L i c) = 1 := by simpa using hnorm.tsum_eq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hV0 : 0 ≤ V := by
    rw [hVar]; exact mul_nonneg hq0 (tsum_nonneg fun c => mul_nonneg (hcomplement c).1 (hQ c))
  have hVq : V ≤ q := by
    rw [hVar]
    have hh := hs.tsum_le_tsum (fun c => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcomplement c).2 (hQ c))
      (by simpa only [one_pow, one_mul] using hnorm.summable)
    rw [htotal] at hh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hq0
  have hP := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ (fun _ => p) (fun _ c => hp c) b hb
  simp only [hmean, card_univ, Fintype.card_fin] at hP
  have hD := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ (fun _ => v) (fun _ c => hv c) t ht
  have hδ : 0 ≤ A * (L : ℝ) ^ 3 / M := by positivity
  have hbudget : 3 * V + 8 * (A * (L : ℝ) ^ 3 / M) * V ^ 2 +
      10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) ≤ B := by
    have hsq : V ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith only [hV0, hVq, hq0]
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8 * (A * (L : ℝ) ^ 3 / M) by positivity)
    dsimp [B]; linarith only [hVq, hh]
  have hD' : (∑ o : Obs M (2 * M * L) e, if t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0) ≤ B / t ^ 2 := by
    apply hD.trans
    simp only [card_univ, Fintype.card_fin]; exact div_le_div_of_nonneg_right hbudget (sq_nonneg t)
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
namespace D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
noncomputable section
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_log
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_lipschitz_certificate
from D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
private theorem native_row_score_offset {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (i : Fin M) (j : Fin 4)
    (hij : nativeRowCell S e o k l i = some j) :
    score q r e o i -
      ((k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
        (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))) =
      offsets r (compensation M q r) j := by
  have hi := (native_row_cell_iff S e o k l i j).mp hij
  unfold score
  rw [hi.2.1, hi.2.2]
  fin_cases j <;> simp [offsets] <;> ring
/-- The full original row calibration is the same one shared by the four
cells. The outside index contains every background row and every signal row
outside the rectangle; no row is discarded. -/
theorem native_full_calibration_sum {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (x : ℝ) :
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
    let outside : {i : Fin M // nativeRowCell S e o k l i = none} → ℝ := fun i => score q r e o i.val - z0
    (∑ i : Fin M, Real.sigmoid (x + (score q r e o i - z0))) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  classical
  dsimp only
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
  let f : Fin M → ℝ := fun i => Real.sigmoid (x + (score q r e o i - z0))
  have hf (j : Fin 4) : (∑ i ∈ univ.filter (fun i => nativeRowCell S e o k l i = some j), f i) =
        C j * Real.sigmoid (x + offsets r (compensation M q r) j) := by
    calc
      _ = ∑ _i ∈ nativeCalibrationCells S e o k l j,
          Real.sigmoid (x + offsets r (compensation M q r) j) := by
        apply sum_congr rfl
        intro i hi
        dsimp only [f]
        rw [native_row_score_offset S r e o k l i j (mem_filter.mp hi).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  have hcounts (j : Fin 4) :
      cellCounts (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) j = C j := by
    fin_cases j <;> dsimp [cellCounts] <;> ring
  have hsum := (sum_fiberwise univ (nativeRowCell S e o k l) f).symm
  rw [Fintype.sum_option] at hsum
  rw [hsum]
  unfold calibratedMean
  change (∑ i with nativeRowCell S e o k l i = none, f i) + (∑ j, ∑ i with nativeRowCell S e o k l i = some j, f i) =
    (∑ i : {i : Fin M // nativeRowCell S e o k l i = none}, f i.val) +
      ∑ j, cellCounts (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) j *
        Real.sigmoid (x + offsets r (compensation M q r) j)
  simp only [hcounts]
  congr 1
  · exact (sum_subtype (univ.filter fun i => nativeRowCell S e o k l i = none)
      (fun i => by simp) f)
  · exact sum_congr rfl (fun j _ => hf j)
private theorem native_calibrated_row_parameter {M q s : ℕ} (r : ℝ)
    (e : Experiment) (o : Obs M s e)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) (i : Fin M) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    Real.sigmoid (score q r e o i - Real.log B0 + Real.log t) =
      t * weight q r e o i / (B0 + t * weight q r e o i) := by
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  have hB0 : 0 < B0 := by apply div_pos <;> exact_mod_cast (by omega : 0 < _)
  have hw := ((finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.2.1 o).2.1 i
  have hexp : Real.exp (score q r e o i - Real.log B0 + Real.log t) =
      t * weight q r e o i / B0 := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log hB0, Real.exp_log ht, ← hw.2]; ring
  dsimp only
  rw [Real.sigmoid_def, Real.exp_neg, hexp]
  change (1 + (t * weight q r e o i / B0)⁻¹)⁻¹ = t * weight q r e o i / (B0 + t * weight q r e o i)
  have hden : B0 + t * weight q r e o i ≠ 0 := ne_of_gt (add_pos hB0 (mul_pos ht hw.1))
  field_simp [ne_of_gt ht, ne_of_gt hw.1, ne_of_gt hB0, hden] <;> try ring
  rw [← add_mul, mul_inv_cancel₀ hden]
/-- The original calibrated Bernoulli parameters, with their original common
multiplicative parameter, use exactly the same full-row four-cell equation. -/
private theorem native_original_calibration_identification {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
    let outside : {i : Fin M // nativeRowCell S e o k l i = none} → ℝ := fun i => score q r e o i.val - z0
    (∑ i : Fin M, t * weight q r e o i / (B0 + t * weight q r e o i)) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  dsimp only
  rw [← native_full_calibration_sum]
  apply sum_congr rfl
  intro i _
  rw [← native_calibrated_row_parameter r e o hq hqm hr hr1 ha ha1 t ht i]
  congr 1
  ring
/-- The original group-zero posterior center and auxiliary Bernoulli center
both use all rows of the same count cell, including background rows. -/
theorem native_group_zero_centers {M q s : ℕ} (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) (i0 : Fin M)
    (hi0 : count e o i0 1 = k ∧ count e o i0 (-1) = l) :
    let All : Support M M := ⟨univ, by simp⟩
    let G := nativeCalibrationCells All e o k l 0
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    (∑ i ∈ G, inclusion q r e o i) = (G.card : ℝ) * inclusion q r e o i0 ∧
    (∑ i ∈ G, t * weight q r e o i / (B0 + t * weight q r e o i)) =
      (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t) := by
  classical
  dsimp only
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e o k l 0
  have hc (i : Fin M) (hi : i ∈ G) :
      count e o i 1 = k ∧ count e o i (-1) = l := by
    have h := (native_row_cell_iff All e o k l i 0).mp (mem_filter.mp hi).2
    simpa using h.2
  have hw (i : Fin M) (hi : i ∈ G) : weight q r e o i = weight q r e o i0 := by
    simp only [weight, (hc i hi).1, (hc i hi).2, hi0.1, hi0.2]
  have ho := ((finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.2.1 o).2.2.2.2
  constructor
  · calc
      _ = ∑ _i ∈ G, inclusion q r e o i0 := by
        apply sum_congr rfl
        intro i hi
        exact le_antisymm ((ho i i0).mpr (le_of_eq (hw i hi))) ((ho i0 i).mpr (le_of_eq (hw i hi).symm))
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  · calc _ = ∑ _i ∈ G, Real.sigmoid ((k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
            (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r)) -
              Real.log (((M - q : ℕ) : ℝ) / (q : ℝ)) + Real.log t) := by
        apply sum_congr rfl
        intro i hi
        rw [← native_calibrated_row_parameter r e o hq hqm hr hr1 ha ha1 t ht i]; simp only [score, (hc i hi).1, (hc i hi).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
/-- The full group-zero size is a fixed background count plus the native
rectangle A count on the same complete collapsed-history fiber. -/
private theorem native_group_zero_count_bridge {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (y : NativeSignalConditionalFiber.Fiber S e o) :
    let All : Support M M := ⟨univ, by simp⟩
    let G := nativeCalibrationCells All e y.val k l 0
    let BG := nativeCalibrationCells All e o k l 0 \ S.val
    G.card = BG.card + RectangleHypergeometricKernel.nativeRectangleACount S e o k l y := by
  classical
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e y.val k l 0
  let BG := nativeCalibrationCells All e o k l 0 \ S.val
  have hG (v : Obs M s e) (i : Fin M) : i ∈ nativeCalibrationCells All e v k l 0 ↔
        count e v i 1 = k ∧ count e v i (-1) = l := by simp [nativeCalibrationCells, native_row_cell_iff, All]
  have hbg : G \ S.val = BG := by
    ext i
    change i ∈ nativeCalibrationCells All e y.val k l 0 \ S.val ↔ i ∈ nativeCalibrationCells All e o k l 0 \ S.val
    simp only [Finset.mem_sdiff, hG]
    by_cases hi : i ∈ S.val
    · simp only [hi, not_true_eq_false, and_false]
    · rw [NativeSignalConditionalFiber.native_background_row_counts S e o y i hi 1,
        NativeSignalConditionalFiber.native_background_row_counts S e o y i hi (-1)]
  have hsig : (G.subtype (fun i => i ∈ S.val)).card =
      RectangleHypergeometricKernel.nativeRectangleACount S e o k l y := by
    congr 1
    ext i
    simp only [mem_subtype, G, hG, RectangleHypergeometricKernel.nativeRectangleACount, mem_filter, mem_univ, true_and]
  have hc := card_sdiff_add_card_inter G S.val
  rw [hbg] at hc
  have hs := card_subtype (fun i => i ∈ S.val) G
  simp only [filter_mem_eq_inter] at hs
  rw [hs] at hsig; exact hc.symm.trans (congrArg (fun n => BG.card + n) hsig)
private theorem sigmoid_log_odds {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Real.sigmoid (Real.log (p / (1 - p))) = p := by
  rw [D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_log (div_pos hp (sub_pos.mpr hp1))]
  field_simp [ne_of_gt (sub_pos.mpr hp1)] <;> ring
/-- The full original group posterior is compared with its common calibrated
center. The mean and variance premises are exactly those of the frozen
posterior-odds theorem; no auxiliary posterior replaces the original one. -/
private theorem native_group_zero_posterior_approximation :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (r : ℝ), 1 ≤ q → q < M → 0 < r → r < 1 →
        compensation M q r < 1 → ∀ (e : Experiment) (o : Obs M s e) (t : ℝ),
          0 < t → ∀ k l : ℕ,
          let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
          let p := fun i : Fin M => t * weight q r e o i / (B0 + t * weight q r e o i)
          let V := ∑ i, p i * (1 - p i)
          let All : Support M M := ⟨univ, by simp⟩
          let G := nativeCalibrationCells All e o k l 0
          let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
            (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
          (∑ i, p i) = (q : ℝ) → V0 ≤ V →
            |(∑ i ∈ G, inclusion q r e o i) -
              (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
                C * (G.card : ℝ) / V := by
  classical
  obtain ⟨C, hC, V0, hV0, hpost⟩ := D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds.result
  refine ⟨C / 4, by positivity, V0, hV0, ?_⟩
  intro M q s r hq hqm hr hr1 ha1 e o t ht k l
  dsimp only
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let p := fun i : Fin M => t * weight q r e o i / (B0 + t * weight q r e o i)
  let V := ∑ i, p i * (1 - p i)
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e o k l 0
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  change (∑ i, p i) = (q : ℝ) → V0 ≤ V → _
  intro hmean hvar
  change |(∑ i ∈ G, inclusion q r e o i) - (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤ C / 4 * (G.card : ℝ) / V
  have ha : 0 ≤ compensation M q r := by unfold compensation; positivity
  by_cases hG : G.Nonempty
  · obtain ⟨i, hi⟩ := hG
    have hi0 : count e o i 1 = k ∧ count e o i (-1) = l := by
      have hi' := (native_row_cell_iff All e o k l i 0).mp (mem_filter.mp hi).2
      simpa using hi'.2
    have hcenters := native_group_zero_centers r e o k l hq hqm hr hr1 ha ha1 t ht i hi0
    change (∑ j ∈ G, inclusion q r e o j) = (G.card : ℝ) * inclusion q r e o i ∧ _ at hcenters
    rw [hcenters.1, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg G.card)]
    have ho := hpost M q s r hq hqm hr hr1 ha1 e o t ht hmean hvar i
    have hlog : score q r e o i - Real.log B0 + Real.log t =
        z0 - Real.log B0 + Real.log t := by simp only [score, hi0.1, hi0.2, z0]
    have hlip := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_lipschitz_certificate.dist_le_mul
      (Real.log (inclusion q r e o i / (1 - inclusion q r e o i)))
      (z0 - Real.log B0 + Real.log t)
    rw [Real.dist_eq, Real.dist_eq, sigmoid_log_odds ho.1 ho.2.1] at hlip
    have herrLog : |Real.log (inclusion q r e o i / (1 - inclusion q r e o i)) -
        (score q r e o i - Real.log B0 + Real.log t)| ≤ C / V := ho.2.2
    rw [hlog] at herrLog
    have herr : |inclusion q r e o i - Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
        (1 / 4 : ℝ) * (C / V) := by exact hlip.trans (mul_le_mul_of_nonneg_left herrLog (by norm_num))
    calc
      _ ≤ (G.card : ℝ) * ((1 / 4 : ℝ) * (C / V)) :=
        mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg G.card)
      _ = _ := by ring
  · have he : G = ∅ := not_nonempty_iff_eq_empty.mp hG
    simp [he]
/-- Every row outside the signal rectangle retains both native counts on
one coarse environment fiber. Background rows are included. -/
theorem native_environment_outside_counts {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (i : Fin M) (hi : nativeRowCell S e z.val k l i = none) :
    count e y.val i 1 = count e z.val i 1 ∧
      count e y.val i (-1) = count e z.val i (-1) ∧
      nativeRowCell S e y.val k l i = none := by
  classical
  by_cases hs : i ∈ S.val
  · let j : {i : Fin M // i ∈ S.val} := ⟨i, hs⟩
    have hn (v : NativeSignalConditionalFiber.Fiber S e o) : nativeRowCell S e v.val k l i = none ↔
          j ∉ RectangleHypergeometricKernel.nativeRectangleRows S e o k l v := by
      simp only [RectangleHypergeometricKernel.nativeRectangleRows, mem_filter, mem_univ, true_and, j]
      simp only [nativeRowCell, hs, ↓reduceIte]
      split_ifs <;> aesop
    have hz := (hn z).mp hi
    have hV := congrArg Prod.fst henv
    change RectangleHypergeometricKernel.nativeRectangleRows S e o k l y =
      RectangleHypergeometricKernel.nativeRectangleRows S e o k l z at hV
    have hy : j ∉ RectangleHypergeometricKernel.nativeRectangleRows S e o k l y := by rwa [hV]
    have he := congrArg (fun v => v.2.1 j) henv
    change (if j ∈ RectangleHypergeometricKernel.nativeRectangleRows S e o k l y then none
      else some (count e y.val j.val 1, count e y.val j.val (-1))) =
      (if j ∈ RectangleHypergeometricKernel.nativeRectangleRows S e o k l z then none
      else some (count e z.val j.val 1, count e z.val j.val (-1))) at he
    simp only [if_neg hy, if_neg hz, Option.some.injEq, Prod.mk.injEq, j] at he; exact ⟨he.1, he.2, (hn y).mpr hy⟩
  · rw [NativeSignalConditionalFiber.native_background_row_counts S e o y i hs 1,
      NativeSignalConditionalFiber.native_background_row_counts S e o z i hs 1,
      NativeSignalConditionalFiber.native_background_row_counts S e o y i hs (-1),
      NativeSignalConditionalFiber.native_background_row_counts S e o z i hs (-1)]
    exact ⟨rfl, rfl, by simp [nativeRowCell, hs]⟩
/-- The original outside logits are fixed by the same numerical-margin
readout as the native hypergeometric law. -/
private theorem native_environment_outside_score {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (i : Fin M) (hi : nativeRowCell S e z.val k l i = none) :
    score q r e y.val i = score q r e z.val i ∧
      nativeRowCell S e y.val k l i = none := by
  have h := native_environment_outside_counts S e o k l y z henv i hi
  exact ⟨by simp only [score, h.1, h.2.1], h.2.2⟩
/-- The all-row calibration on a native rectangle environment uses one
fixed outside function. Only the four cell multiplicities change. -/
private theorem native_environment_calibration_identification {M q s : ℕ}
    (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e y.val k l j).card
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  classical
  dsimp only
  rw [native_original_calibration_identification S r e y.val k l hq hqm hr hr1 ha ha1 t ht]
  unfold calibratedMean
  congr 1
  have hn (i : Fin M) : nativeRowCell S e y.val k l i = none ↔ nativeRowCell S e z.val k l i = none :=
    ⟨fun hi => (native_environment_outside_score S r e o k l z y henv.symm i hi).2,
      fun hi => (native_environment_outside_score S r e o k l y z henv i hi).2⟩
  let E := Equiv.subtypeEquivRight hn
  apply Fintype.sum_equiv E
  intro i
  have hi := native_environment_outside_score S r e o k l z y henv.symm i.val i.property
  simp only [E, Equiv.subtypeEquivRight_apply, hi.1]
/-- The original full calibration on one environment fiber is exactly the
moving four-cell equation with the native N, R, U, and A count. -/
private theorem native_environment_full_calibration {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let V := RectangleHypergeometricKernel.nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let A := RectangleHypergeometricKernel.nativeRectangleACount S e o k l y
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r) V.card R U A x := by
  classical
  dsimp only
  rw [native_environment_calibration_identification S r e o k l y z henv hq hqm hr hr1 ha ha1 t ht]
  have hc := native_calibration_counts_margins S e o k l y
  dsimp only at hc
  have hV := congrArg (fun v => v.1.card) henv
  have hR := congrArg (fun v => v.2.2.1) henv
  have hU := congrArg (fun v => v.2.2.2) henv
  change (RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).card =
    (RectangleHypergeometricKernel.nativeRectangleRows S e o k l z).card at hV
  change ((RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).filter
    fun i => count e y.val i.val 1 = k).card = _ at hR
  change ((RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).filter
    fun i => count e y.val i.val (-1) = l).card = _ at hU
  congr 1
  · simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ)) (hc.1.symm.trans hV)
  · simpa only [Nat.cast_add, RectangleHypergeometricKernel.nativeMarginRectangleReadout] using
      congrArg (fun n : ℕ => (n : ℝ)) (hc.2.1.symm.trans hR)
  · simpa only [Nat.cast_add, RectangleHypergeometricKernel.nativeMarginRectangleReadout] using
      congrArg (fun n : ℕ => (n : ℝ)) (hc.2.2.1.symm.trans hU)
  · exact congrArg (fun n : ℕ => (n : ℝ)) hc.2.2.2.symm
end
end D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
set_option maxHeartbeats 800000
namespace D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
noncomputable section
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
from D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
/-- The native environment fixes the complete sigmoid equation, including
its derivative. The variance is not supplied as an independent surrogate. -/
theorem native_environment_mean_variance {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l : ℕ)
    (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1) (x : ℝ) :
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let A := nativeRectangleACount S e o k l y
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, Real.sigmoid (x + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A x ∧
    (∑ i : Fin M, Real.sigmoid (x + (score q r e y.val i - z0)) *
      (1 - Real.sigmoid (x + (score q r e y.val i - z0)))) =
        calibratedVariance outside r (compensation M q r) V.card R U A x := by
  classical
  dsimp only
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let A := nativeRectangleACount S e o k l y
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val - z0
  have he := (native_minimal_readout_eq_iff S e o k l y z).mp henv
  have hf (u : ℝ) : (∑ i : Fin M, Real.sigmoid (u + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A u := by
    let t := Real.exp (u - z0 + Real.log B0)
    have ht : 0 < t := Real.exp_pos _
    have hc := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_environment_full_calibration
      S r e o k l y z he hq hqm hr hr1 ha ha1 t ht
    dsimp only at hc
    have hx : z0 - Real.log B0 + Real.log t = u := by rw [Real.log_exp]; ring
    change (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r) V.card R U A
        (z0 - Real.log B0 + Real.log t) at hc
    rw [hx] at hc
    rw [← hc]
    apply sum_congr rfl
    intro i _
    rw [← D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
      r e y.val hq hqm hr hr1 ha ha1 t ht i]
    congr 1
    linarith [hx]
  refine ⟨hf x, ?_⟩
  have hfun : (∑ i : Fin M, fun u : ℝ => Real.sigmoid (u + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A := by
    ext u
    simp only [Finset.sum_apply]; exact hf u
  have hd := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin M))) =>
    D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv
      (score q r e y.val i - z0) x)
  rw [hfun] at hd; exact hd.unique (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
    outside r (compensation M q r) V.card R U A x)
/-- The integer target keeps the parity forced by the original harmonic
and count. Half-integer shifts are preserved before any set enlargement. -/
theorem posterior_phase_iff_parity_band (ell t : ℤ) (mu τ : ℝ) :
    (∃ a : ℤ, |(ell : ℝ)*(1/2-mu)-a| ≤ τ) ↔
      ∃ z : ℤ, Int.ModEq 2 z (ell*(1-t)) ∧
        |2*(ell : ℝ)*(mu-(t : ℝ)/2)-z| ≤ 2*τ := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨ell-2*a-ell*t,Int.modEq_iff_dvd.mpr ⟨a,by ring⟩,?_⟩
    have he : 2*(ell : ℝ)*(mu-(t : ℝ)/2)-((ell-2*a-ell*t : ℤ) : ℝ) =
        -2*((ell : ℝ)*(1/2-mu)-a) := by push_cast; ring
    rw [he,abs_mul]; norm_num
    linarith only [ha]
  · rintro ⟨z,hmod,hz⟩
    obtain ⟨a,ha⟩ := Int.modEq_iff_dvd.mp hmod
    refine ⟨a,?_⟩
    have hez : z = ell-2*a-ell*t := by linear_combination -ha
    rw [hez] at hz
    have he : 2*(ell : ℝ)*(mu-(t : ℝ)/2)-((ell-2*a-ell*t : ℤ) : ℝ) =
        -2*((ell : ℝ)*(1/2-mu)-a) := by push_cast; ring
    rw [he,abs_mul] at hz; norm_num at hz
    linarith only [hz]
/-- A half-lattice enlargement removes the parity split uniformly for
positive and negative harmonics. The approximation is for the original mu. -/
private theorem posterior_phase_lattice_reduction (ell t : ℤ) (mu bg x τ err : ℝ)
    (happrox : |mu-(bg+(t : ℝ))*Real.sigmoid x| ≤ err)
    (hphase : ∃ z : ℤ, |(ell : ℝ)*(1/2-mu)-z| ≤ τ) :
    ∃ z : ℤ, |2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-(t : ℝ)/2)-z| ≤
      2*τ+2*|(ell : ℝ)| *err := by
  obtain ⟨z,_,hz⟩ := (posterior_phase_iff_parity_band ell t mu τ).mp hphase
  refine ⟨z,?_⟩
  have he : 2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-(t : ℝ)/2)-z = (2*(ell : ℝ)*(mu-(t : ℝ)/2)-z)+
        2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-mu) := by ring
  rw [he]
  calc
    _ ≤ |2*(ell : ℝ)*(mu-(t : ℝ)/2)-z|+
        |2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-mu)| := abs_add_le _ _
    _ ≤ 2*τ+2*|(ell : ℝ)| *err := by
      rw [abs_mul,abs_mul,abs_sub_comm ((bg+(t : ℝ))*Real.sigmoid x) mu]; norm_num
      exact add_le_add hz (mul_le_mul_of_nonneg_left happrox (by positivity))
/-- The full original posterior is approximated by the same native shared
root. Its error is proved from frozen posterior odds and the exact all-row
mean and variance identification. -/
private theorem native_environment_posterior_approximation :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e),
        ∀ [Fintype (Sites s e)], 1 ≤ q → q < M → 0 < r → r < 1 →
          0 ≤ compensation M q r → compensation M q r < 1 →
          ∀ (k l : ℕ) (y z : Fiber S e o),
            nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z →
            ∀ x : ℝ,
            let All : Support M M := ⟨univ, by simp⟩
            let G := nativeCalibrationCells All e y.val k l 0
            let BG := nativeCalibrationCells All e o k l 0 \ S.val
            let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
              (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
            let V := nativeRectangleRows S e o k l z
            let R := (V.filter fun i => count e z.val i.val 1 = k).card
            let U := (V.filter fun i => count e z.val i.val (-1) = l).card
            let A := nativeRectangleACount S e o k l y
            let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val - z0
            calibratedMean outside r (compensation M q r) V.card R U A x = q →
            V0 ≤ calibratedVariance outside r (compensation M q r) V.card R U A x →
              |(∑ i ∈ G, inclusion q r e y.val i) - ((BG.card : ℝ) + A) * Real.sigmoid x| ≤
                C * ((BG.card : ℝ) + A) /
                  calibratedVariance outside r (compensation M q r) V.card R U A x := by
  classical
  obtain ⟨C, hC, V0, hV0, hp⟩ := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_posterior_approximation
  refine ⟨C, hC, V0, hV0, ?_⟩
  intro M q s S r e o _ hq hqm hr hr1 ha ha1 k l y z henv x
  dsimp only
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) + (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let t := Real.exp (x - z0 + Real.log B0)
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let A := nativeRectangleACount S e o k l y
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val - z0
  let p := fun i : Fin M => t * weight q r e y.val i / (B0 + t * weight q r e y.val i)
  intro hmean hvar
  have ht : 0 < t := Real.exp_pos _
  have hx : z0 - Real.log B0 + Real.log t = x := by rw [Real.log_exp]; ring
  have hrow (i : Fin M) : p i = Real.sigmoid (x + (score q r e y.val i - z0)) := by
    dsimp only [p]
    rw [← D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
      r e y.val hq hqm hr hr1 ha ha1 t ht i]
    congr 1
    linarith [hx]
  have hi := native_environment_mean_variance S r e o k l y z henv hq hqm hr hr1 ha ha1 x
  dsimp only at hi
  have hpm : (∑ i, p i) = (q : ℝ) := by
    simp_rw [hrow]
    exact hi.1.trans hmean
  have hpv : (∑ i, p i * (1 - p i)) =
      calibratedVariance outside r (compensation M q r) V.card R U A x := by
    simp_rw [hrow]
    exact hi.2
  have hh := hp M q s r hq hqm hr hr1 ha1 e y.val t ht k l hpm (hpv.symm ▸ hvar)
  dsimp only at hh
  have hgroup := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_count_bridge S e o k l y
  dsimp only at hgroup
  change |(∑ i ∈ nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0, inclusion q r e y.val i) -
      ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0).card : ℝ) *
        Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
    C * ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0).card : ℝ) /
      (∑ i, p i * (1 - p i)) at hh
  rw [hx, hpv, hgroup] at hh
  simpa only [Nat.cast_add] using hh
/-- The original posterior phase is covered centrally by a lattice band.
Outside the central interval the original count tail is retained unchanged. -/
theorem native_posterior_central_kernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e),
        ∀ [Fintype (Sites s e)], 1 ≤ q → q < M → 0 < r → r < 1 →
          0 ≤ compensation M q r → compensation M q r < 1 →
          ∀ (k l : ℕ) (z : Fiber S e o) (θ : ℝ → ℝ) (ell : ℤ) (τ w D : ℝ),
            letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
            let All : Support M M := ⟨univ, by simp⟩
            let BG := nativeCalibrationCells All e o k l 0 \ S.val
            let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r)) + (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
            let V := nativeRectangleRows S e o k l z
            let R := (V.filter fun i => count e z.val i.val 1 = k).card
            let U := (V.filter fun i => count e z.val i.val (-1) = l).card
            let ν : ℝ := (U : ℝ)*R/V.card
            let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val-z0
            let Env := univ.filter fun y : Fiber S e o =>
              nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
            let Q := fun y : Fiber S e o => ∃ a : ℤ,
              |(ell : ℝ)*(1/2-
                (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i))-a| ≤ τ
            let P := fun t : ℕ => w < |(t : ℝ)-ν| ∨ ∃ a : ℤ,
              |2*(ell : ℝ)*(((BG.card : ℝ)+t)*Real.sigmoid (θ t)-(t : ℝ)/2)-a| ≤
                2*τ+2 * |(ell : ℝ)| * (C*((BG.card : ℝ)+ν+w)/D)
            letI : DecidablePred Q := Classical.decPred Q
            letI : DecidablePred P := Classical.decPred P
            V0 ≤ D →
            (∀ y ∈ Env, |(nativeRectangleACount S e o k l y : ℝ)-ν| ≤ w →
              calibratedMean outside r (compensation M q r) V.card R U
                (nativeRectangleACount S e o k l y) (θ (nativeRectangleACount S e o k l y)) = q) →
            (∀ y ∈ Env, |(nativeRectangleACount S e o k l y : ℝ)-ν| ≤ w →
              D ≤ calibratedVariance outside r (compensation M q r) V.card R U
                (nativeRectangleACount S e o k l y) (θ (nativeRectangleACount S e o k l y))) →
            conditionalFiberMass S r e o (Env.filter Q) / conditionalFiberMass S r e o Env ≤
              ∑ t ∈ (range (U+1)).filter P,
                (if t ≤ U then ((R.choose t : ℝ)*((V.card-R).choose (U-t) : ℝ)) /
                  (V.card.choose U : ℝ) else 0) := by
  classical
  obtain ⟨C,hC,V0,hV0,hpost⟩ := native_environment_posterior_approximation
  refine ⟨C,hC,V0,hV0,?_⟩
  intro M q s S r e o _ hq hqm hr hr1 ha ha1 k l z θ ell τ w D
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let All : Support M M := ⟨univ, by simp⟩
  let BG := nativeCalibrationCells All e o k l 0 \ S.val
  let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r)) + (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let ν : ℝ := (U : ℝ)*R/V.card
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ := fun i => score q r e z.val i.val-z0
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  intro hD hmean hvar
  let Q' : Fiber S e o → Prop := fun y => ∃ a : ℤ,
    |(ell : ℝ) * (1 / 2 -
      (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i)) - a| ≤ τ
  let P' : ℕ → Prop := fun t => w < |(t : ℝ)-ν| ∨ ∃ a : ℤ,
    |2 * (ell : ℝ) * (((BG.card : ℝ)+t)*Real.sigmoid (θ t)-(t : ℝ)/2)-a| ≤
      2*τ + 2 * |(ell : ℝ)| * (C*((BG.card : ℝ)+ν+w)/D)
  letI : DecidablePred Q' := Classical.decPred Q'
  letI : DecidablePred P' := Classical.decPred P'
  have hpush : ∀ y, nativeMinimalRectangleReadout S e o k l y =
      nativeMinimalRectangleReadout S e o k l z → Q' y → P' (nativeRectangleACount S e o k l y) := by
    intro y henv hphase
    by_cases hc : |(nativeRectangleACount S e o k l y : ℝ)-ν| ≤ w
    · right
      have hy : y ∈ Env := by simp only [Env,mem_filter,mem_univ,true_and]; exact henv
      have hv := hvar y hy hc
      have happrox := hpost M q s S r e o hq hqm hr hr1 ha ha1 k l y z henv
        (θ (nativeRectangleACount S e o k l y)) (hmean y hy hc) (hD.trans hv)
      have hnum : (BG.card : ℝ)+nativeRectangleACount S e o k l y ≤ (BG.card : ℝ)+ν+w := by linarith [(abs_le.mp hc).2]
      have hnum0 : 0 ≤ (BG.card : ℝ)+ν+w := (by positivity : 0 ≤ (BG.card : ℝ)+nativeRectangleACount S e o k l y).trans hnum
      have herr : |(∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i) -
          ((BG.card : ℝ)+nativeRectangleACount S e o k l y)*
            Real.sigmoid (θ (nativeRectangleACount S e o k l y))| ≤ C*((BG.card : ℝ)+ν+w)/D := by
        exact happrox.trans (div_le_div₀ (mul_nonneg hC.le hnum0) (mul_le_mul_of_nonneg_left hnum hC.le) (hV0.trans_le hD) hv)
      simpa only [Int.cast_natCast] using posterior_phase_lattice_reduction ell (nativeRectangleACount S e o k l y)
        (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i)
        BG.card (θ (nativeRectangleACount S e o k l y)) τ (C*((BG.card : ℝ)+ν+w)/D)
        (by simpa only [Int.cast_natCast] using herr) hphase
    · exact Or.inl (lt_of_not_ge hc)
  have hp := native_event_mass_le_kernel S r e o hq hqm hr hr1 ha ha1 k l z Q' P' hpush
  simpa only [Q',P'] using hp
/-- Balanced margins give one root curve on an open neighborhood of the
whole central interval, not a collection of separately chosen roots. -/
theorem balanced_shared_curve {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q δ w : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N) (hδ : 0 < δ) (hw : w ≤ δ^2*N/2)
    (hRlo : δ*N ≤ R) (hRhi : R ≤ (1-δ)*N)
    (hUlo : δ*N ≤ U) (hUhi : U ≤ (1-δ)*N) :
    ∃ θ : ℝ → ℝ, ∀ t : ℝ, |t-U*R/N| ≤ w →
      calibratedMean outside r ε N R U t (θ t) = q ∧
      HasDerivAt θ (-checkerboard r ε (θ t) /
        calibratedVariance outside r ε N R U t (θ t)) t ∧
      (∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q) ∧
      0 < calibratedVariance outside r ε N R U t (θ t) := by
  let ν := U*R/N
  let v := δ^2*N
  have hv : 0 < v := by dsimp [v]; positivity
  have hcells (t : ℝ) (ht : t ∈ Set.Ioo (ν-v) (ν+v)) (j : Fin 4) :
      0 ≤ cellCounts N R U t j := by
    have hc := central_four_cells_lower N R U δ t v hN hδ.le hRlo hRhi hUlo hUhi
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) j
    dsimp [v] at hc; linarith
  obtain ⟨θ,hθ⟩ := shared_calibration_curve outside r ε N R U q (ν-v) (ν+v) hN hq hqM hcells
  refine ⟨θ, fun t ht => ?_⟩
  have hti : t ∈ Set.Ioo (ν-v) (ν+v) := by
    have hb := abs_le.mp ht
    dsimp [v,ν] at *
    constructor <;> nlinarith
  have he := hθ t hti
  refine ⟨he.1,he.2.1,?_,he.2.2⟩
  filter_upwards [isOpen_Ioo.mem_nhds hti] with u hu
  exact (hθ u hu).1
/-- The rectangle and all remaining candidate rows partition the original
M rows, so the root range uses the original support-size condition. -/
theorem native_outside_rectangle_card {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (z : Fiber S e o) :
    Fintype.card {i : Fin M // nativeRowCell S e z.val k l i = none} +
      (nativeRectangleRows S e o k l z).card = M := by
  classical
  have hn := (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibration_counts_margins S e o k l z).1
  have he := sum_fiberwise (univ : Finset (Fin M)) (nativeRowCell S e z.val k l) (fun _ => (1 : ℕ))
  rw [Fintype.sum_option] at he; simp only [sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin,
    Fin.sum_univ_four] at he
  rw [hn, Fintype.card_subtype]; simp only [nativeCalibrationCells,add_assoc] at *
  convert he using 1 <;> congr 1
  all_goals ext i; simp only [mem_filter]
end
end D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
