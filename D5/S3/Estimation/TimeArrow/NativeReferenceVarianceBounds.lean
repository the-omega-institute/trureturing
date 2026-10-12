/- GID: D5/S3/Estimation/TimeArrow/NativeReferenceVarianceBounds
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeReferenceVarianceBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete reference calibration variance is bounded below by actual count-window mass. -/

import D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
import D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
import Mathlib.Probability.Distributions.Poisson.Basic

open scoped BigOperators
open Finset ProbabilityTheory
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeReferenceCalibration


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeReferenceVarianceBounds
noncomputable section

private theorem poisson_atom_lower (mu : ℝ) (hmu : 0 < mu) {n : ℕ} (hn : 0 < n) :
    Real.exp (-((n : ℝ) - mu) ^ 2 / mu - 1) / Real.sqrt n ≤
      Real.exp (-mu) * mu ^ n / n.factorial := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmuR : (0 : ℝ) < mu := hmu
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hs := (D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.log_factorial_envelopes hn).2
  have hl := Real.log_le_sub_one_of_pos (div_pos hnR hmuR)
  rw [Real.log_div hnR.ne' hmuR.ne'] at hl
  have he : (n : ℝ) * ((n : ℝ) / mu - 1) - n + mu = ((n : ℝ) - mu) ^ 2 / mu := by
    field_simp
    <;> ring
  have hh := mul_le_mul_of_nonneg_left hl hnR.le
  have hrate : (n : ℝ) * (Real.log n - Real.log mu) - n + mu ≤
      ((n : ℝ) - mu) ^ 2 / mu := by linarith only [hh, he]
  have hp : 0 < Real.exp (-(mu : ℝ)) * (mu : ℝ) ^ n / n.factorial := by positivity
  have hlog : -((n : ℝ) - mu) ^ 2 / mu - 1 - Real.log n / 2 ≤
      Real.log (Real.exp (-(mu : ℝ)) * (mu : ℝ) ^ n / n.factorial) := by
    rw [Real.log_div (by positivity) hf.ne',
      Real.log_mul (Real.exp_pos _).ne' (pow_pos hmuR n).ne', Real.log_exp, Real.log_pow]
    rw [mul_sub] at hrate
    simp only [neg_div] at hrate ⊢
    linarith only [hs, hrate]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp] at hexp
  calc
    _ = Real.exp (-((n : ℝ) - mu) ^ 2 / mu - 1 - Real.log n / 2) := by
      rw [← Real.log_sqrt hnR.le,
        Real.exp_sub (-((n : ℝ) - mu) ^ 2 / mu - 1) (Real.log (Real.sqrt n)),
        Real.exp_log (Real.sqrt_pos.mpr hnR)]
    _ ≤ _ := hexp

private theorem poisson_window_lower (c K lam : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hlam : 0 < lam) {n : ℕ} (hn : 0 < n) (hwindow : |(n : ℝ) - c * lam| ≤ K * Real.sqrt lam)
    (hupper : (n : ℝ) ≤ (3 / 2) * c * lam) :
    Real.exp (-K ^ 2 / c - 1) / (Real.sqrt ((3 / 2) * c) * Real.sqrt lam) ≤
      Real.exp (-(c * lam)) * (c * lam) ^ n / n.factorial := by
  have hmu : 0 < c * lam := mul_pos hc hlam
  have hbase := poisson_atom_lower (c * lam) hmu hn
  have hsq : ((n : ℝ) - c * lam) ^ 2 ≤ K ^ 2 * lam := by
    have hh := mul_self_le_mul_self (abs_nonneg ((n : ℝ) - c * lam)) hwindow
    have hs := Real.sq_sqrt hlam.le
    rw [← pow_two, sq_abs] at hh
    nlinarith only [hh, hs]
  have hr : ((n : ℝ) - c * lam) ^ 2 / (c * lam) ≤ K ^ 2 / c := by
    apply (div_le_iff₀ (mul_pos hc hlam)).mpr
    have he : K ^ 2 / c * (c * lam) = K ^ 2 * lam := by field_simp
    rw [he]
    exact hsq
  have hnum : Real.exp (-K ^ 2 / c - 1) ≤
      Real.exp (-((n : ℝ) - c * lam) ^ 2 / (c * lam) - 1) :=
    Real.exp_le_exp.mpr (by
      simpa only [neg_div] using sub_le_sub_right (neg_le_neg hr) 1)
  have hden : Real.sqrt n ≤ Real.sqrt ((3 / 2) * c) * Real.sqrt lam := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hupper
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_div₀ (Real.exp_pos _).le hnum (Real.sqrt_pos.mpr hnR) hden).trans hbase

open private
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
from D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open private D5.S3.Estimation.TimeArrow.NativeReferenceCalibration.all_row_reference_sum
from D5.S3.Estimation.TimeArrow.NativeReferenceCalibration

/-- Any finite signal count window below the calibration threshold gives a
lower bound for the complete reference variance; all other rows remain in it. -/
theorem reference_variance_count_window {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val)
    (D : Finset (ℕ × ℕ)) (hD : ∀ c ∈ D, referenceParameter M q r c ≤ 1 / 2) :
    (q : ℝ) / 2 * (∑ c ∈ D, rowReference S r L i c) ≤
      (q : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L j c) := by
  have hcal := (reference_calibration_mean_variance S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj).2
  rw [hcal]
  have hqR : (0 : ℝ) ≤ q := by positivity
  have hg (c : ℕ × ℕ) : 0 ≤ 1 - referenceParameter M q r c ∧
      1 - referenceParameter M q r c ≤ 1 := by
    have hp := Real.sigmoid_nonneg (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r)) - Real.log (((M - q : ℕ) : ℝ) / q))
    have hp1 := Real.sigmoid_le_one (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r)) - Real.log (((M - q : ℕ) : ℝ) / q))
    change 0 ≤ referenceParameter M q r c at hp
    change referenceParameter M q r c ≤ 1 at hp1
    constructor <;> linarith only [hp, hp1]
  have hs := (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
    S r κ hκ hr hrκ hcκ hL i (fun c => 1 - referenceParameter M q r c) hg).1
  have hsum := hs.sum_le_tsum D (fun c _ => mul_nonneg (hg c).1
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le)
  have hl : (1 / 2) * (∑ c ∈ D, rowReference S r L i c) ≤
      ∑ c ∈ D, (1 - referenceParameter M q r c) * rowReference S r L i c := by
    rw [mul_sum]
    apply sum_le_sum
    intro c hc
    exact mul_le_mul_of_nonneg_right (by linarith [hD c hc])
      (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hh := mul_le_mul_of_nonneg_left (hl.trans hsum) hqR
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hh

/-- The two signal Poisson coordinates supply an explicit mass for every
finite rectangle contained in a square-root window. -/
theorem signal_rectangle_mass_lower {M q L : ℕ} (S : Support M q)
    (r K : ℝ) (hr : 0 < r) (hr1 : r < 1) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val) (D : Finset (ℕ × ℕ))
    (hD : ∀ c ∈ D, 0 < c.1 ∧ 0 < c.2 ∧
      |(c.1 : ℝ) - ((1 + r) / 2) * L| ≤ K * Real.sqrt L ∧
      |(c.2 : ℝ) - ((1 - r) / 2) * L| ≤ K * Real.sqrt L ∧
      (c.1 : ℝ) ≤ (3 / 2) * ((1 + r) / 2) * L ∧
      (c.2 : ℝ) ≤ (3 / 2) * ((1 - r) / 2) * L) :
    (D.card : ℝ) *
      (Real.exp (-K ^ 2 / ((1 + r) / 2) - 1) *
        Real.exp (-K ^ 2 / ((1 - r) / 2) - 1) /
        (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
          Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L)) ≤
      ∑ c ∈ D, rowReference S r L i c := by
  have hlam : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have ha : 0 < (1 + r) / 2 := by linarith
  have hb : 0 < (1 - r) / 2 := by linarith
  rw [← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro c hc
  obtain ⟨hn, hm, hw, hv, hu, hz⟩ := hD c hc
  have hp := poisson_window_lower ((1 + r) / 2) K L ha hK hlam hn hw hu
  have hq := poisson_window_lower ((1 - r) / 2) K L hb hK hlam hm hv hz
  have hh := mul_le_mul hp hq (by positivity) (by positivity)
  have hs := Real.sq_sqrt hlam.le
  have hd : (Real.sqrt ((3 / 2) * ((1 + r) / 2)) * Real.sqrt L) *
      (Real.sqrt ((3 / 2) * ((1 - r) / 2)) * Real.sqrt L) =
      Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
        Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L := by
    calc
      _ = (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
        Real.sqrt ((3 / 2) * ((1 - r) / 2))) * (Real.sqrt L) ^ 2 := by ring
      _ = _ := by rw [hs]
  rw [← mul_div_mul_comm, hd] at hh
  rw [show ((1 + r) / 2) * (L : ℝ) = (L : ℝ) * (1 + r) / 2 by ring,
    show ((1 - r) / 2) * (L : ℝ) = (L : ℝ) * (1 - r) / 2 by ring] at hh
  unfold rowReference
  simp only [b, if_pos hi]
  exact hh

/-- A finite signal square-root window supplies the full reference variance
with no deletion of the remaining signal or background counts. -/
theorem reference_variance_window_lower {M q L : ℕ} (S : Support M q) (r κ K : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (hK : 0 ≤ K) (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val)
    (D : Finset (ℕ × ℕ))
    (hwindow : ∀ c ∈ D, 0 < c.1 ∧ 0 < c.2 ∧
      |(c.1 : ℝ) - ((1 + r) / 2) * L| ≤ K * Real.sqrt L ∧
      |(c.2 : ℝ) - ((1 - r) / 2) * L| ≤ K * Real.sqrt L ∧
      (c.1 : ℝ) ≤ (3 / 2) * ((1 + r) / 2) * L ∧
      (c.2 : ℝ) ≤ (3 / 2) * ((1 - r) / 2) * L)
    (hscore : ∀ c ∈ D, referenceParameter M q r c ≤ 1 / 2) :
    (q : ℝ) / 2 * (D.card : ℝ) *
      (Real.exp (-K ^ 2 / ((1 + r) / 2) - 1) *
        Real.exp (-K ^ 2 / ((1 - r) / 2) - 1) /
        (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
          Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L)) ≤
      (q : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L j c) := by
  have hm := signal_rectangle_mass_lower S r K hr (by linarith) hK hL i hi D hwindow
  have hv := reference_variance_count_window S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj D hscore
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (q : ℝ) / 2 by positivity)
  apply le_trans _ hv
  simpa only [mul_assoc] using hh

private theorem natural_interval_card_lower (lo hi t : ℝ) (hlo : 0 ≤ lo)
    (ht : 2 ≤ t) (hwidth : hi - lo = t) :
    t / 2 ≤ ((Icc ⌈lo⌉₊ ⌊hi⌋₊).card : ℝ) := by
  have ha := Nat.ceil_lt_add_one hlo
  have hb := Nat.sub_one_lt_floor hi
  have habR : (⌈lo⌉₊ : ℝ) ≤ ⌊hi⌋₊ := by linarith only [ha, hb, ht, hwidth]
  have hab : ⌈lo⌉₊ ≤ ⌊hi⌋₊ := by exact_mod_cast habR
  rw [Nat.card_Icc, Nat.cast_sub (by omega : ⌈lo⌉₊ ≤ ⌊hi⌋₊ + 1), Nat.cast_add, Nat.cast_one]
  linarith only [ha, hb, ht, hwidth]

/-- A concrete lower-left, upper-right count box gives a linear lower bound
for the complete reference variance. All scale and score conditions are
finite inequalities in the original compensated parameters. -/
theorem reference_linear_variance_lower {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 4 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val)
    (hplus : 4 * Real.sqrt L ≤ ((1 + r) / 2) * L)
    (hminus : 4 * Real.sqrt L ≤ ((1 - r) / 2) * L)
    (hcenter :
      (((1 + r) / 2) * L) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (((1 - r) / 2) * L) * Real.log ((1 - r) / (1 + compensation M q r)) -
        Real.log (((M - q : ℕ) : ℝ) / q) ≤
      Real.sqrt L * (Real.log ((1 + r) / (1 - compensation M q r)) -
        Real.log ((1 - r) / (1 + compensation M q r)))) :
    (q : ℝ) / 8 *
      (Real.exp (-(2 : ℝ) ^ 2 / ((1 + r) / 2) - 1) *
        Real.exp (-(2 : ℝ) ^ 2 / ((1 - r) / 2) - 1) /
        (Real.sqrt ((3 / 2) * ((1 + r) / 2)) *
          Real.sqrt ((3 / 2) * ((1 - r) / 2)))) ≤
      ∑ k : Fin M, ∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L k c := by
  classical
  let t := Real.sqrt (L : ℝ)
  let a := ((1 + r) / 2) * L
  let b := ((1 - r) / 2) * L
  let A := Icc ⌈a - 2 * t⌉₊ ⌊a - t⌋₊
  let B := Icc ⌈b + t⌉₊ ⌊b + 2 * t⌋₊
  let D := A ×ˢ B
  have hLam : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have ht : 2 ≤ t := by
    dsimp [t]
    have hh : Real.sqrt (4 : ℝ) ≤ Real.sqrt L :=
      Real.sqrt_le_sqrt (by exact_mod_cast hL)
    norm_num at hh ⊢
    exact hh
  have ht0 : 0 ≤ t := by positivity
  have hsq : t ^ 2 = L := Real.sq_sqrt hLam.le
  have ha : 4 * t ≤ a := hplus
  have hb : 4 * t ≤ b := hminus
  have hcardA := natural_interval_card_lower (a - 2 * t) (a - t) t
    (by linarith only [ha, ht]) ht (by ring)
  have hcardB := natural_interval_card_lower (b + t) (b + 2 * t) t
    (by linarith only [hb, ht]) ht (by ring)
  have hcard : (L : ℝ) / 4 ≤ D.card := by
    dsimp [D]
    rw [card_product, Nat.cast_mul]
    have hh := mul_le_mul hcardA hcardB (by positivity) (by positivity)
    nlinarith only [hh, hsq]
  have hwindow (c : ℕ × ℕ) (hc : c ∈ D) :
      a - 2 * t ≤ c.1 ∧ (c.1 : ℝ) ≤ a - t ∧
      b + t ≤ c.2 ∧ (c.2 : ℝ) ≤ b + 2 * t := by
    have hh := mem_product.mp hc
    have hp := mem_Icc.mp hh.1
    have hm := mem_Icc.mp hh.2
    have hp1 : (⌈a - 2 * t⌉₊ : ℝ) ≤ c.1 := by exact_mod_cast hp.1
    have hp2 : (c.1 : ℝ) ≤ ⌊a - t⌋₊ := by exact_mod_cast hp.2
    have hm1 : (⌈b + t⌉₊ : ℝ) ≤ c.2 := by exact_mod_cast hm.1
    have hm2 : (c.2 : ℝ) ≤ ⌊b + 2 * t⌋₊ := by exact_mod_cast hm.2
    exact ⟨(Nat.le_ceil _).trans hp1,
      hp2.trans (Nat.floor_le (by linarith only [ha, ht])),
      (Nat.le_ceil _).trans hm1,
      hm2.trans (Nat.floor_le (by linarith only [hb, ht]))⟩
  have hw (c : ℕ × ℕ) (hc : c ∈ D) : 0 < c.1 ∧ 0 < c.2 ∧
      |(c.1 : ℝ) - ((1 + r) / 2) * L| ≤ 2 * Real.sqrt L ∧
      |(c.2 : ℝ) - ((1 - r) / 2) * L| ≤ 2 * Real.sqrt L ∧
      (c.1 : ℝ) ≤ (3 / 2) * ((1 + r) / 2) * L ∧
      (c.2 : ℝ) ≤ (3 / 2) * ((1 - r) / 2) * L := by
    obtain ⟨hp, hp', hm, hm'⟩ := hwindow c hc
    have hn : (0 : ℝ) < c.1 := by linarith only [hp, ha, ht]
    have hm0 : (0 : ℝ) < c.2 := by linarith only [hm, hb, ht]
    refine ⟨by exact_mod_cast hn, by exact_mod_cast hm0, ?_, ?_, ?_, ?_⟩
    · apply abs_le.mpr
      change - (2 * t) ≤ (c.1 : ℝ) - a ∧ (c.1 : ℝ) - a ≤ 2 * t
      constructor <;> linarith only [hp, hp', ht]
    · apply abs_le.mpr
      change - (2 * t) ≤ (c.2 : ℝ) - b ∧ (c.2 : ℝ) - b ≤ 2 * t
      constructor <;> linarith only [hm, hm', ht]
    · simp only [mul_assoc]
      change (c.1 : ℝ) ≤ (3 / 2) * a
      linarith only [hp', ha, ht]
    · simp only [mul_assoc]
      change (c.2 : ℝ) ≤ (3 / 2) * b
      linarith only [hm', hb]
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have he : 0 ≤ compensation M q r := by unfold compensation; positivity
  have he1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hu : 0 ≤ Real.log ((1 + r) / (1 - compensation M q r)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by linarith only [he1])).mpr
    linarith only [hr, he]
  have hv : Real.log ((1 - r) / (1 + compensation M q r)) ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hr, he]
  have hp (c : ℕ × ℕ) (hc : c ∈ D) : referenceParameter M q r c ≤ 1 / 2 := by
    obtain ⟨_, hk, hl, _⟩ := hwindow c hc
    have hx := mul_le_mul_of_nonneg_right hk hu
    have hy := mul_le_mul_of_nonpos_right hl hv
    unfold referenceParameter
    have hscore : (c.1 : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
        (c.2 : ℝ) * Real.log ((1 - r) / (1 + compensation M q r)) -
        Real.log (((M - q : ℕ) : ℝ) / q) ≤ 0 := by
      dsimp [a, b, t] at hx hy
      nlinarith only [hx, hy, hcenter]
    have hh := Real.sigmoid_le hscore
    simpa only [Real.sigmoid_zero, one_div] using hh
  have hbound := reference_variance_window_lower S r κ 2 hκ hr hrκ hcκ
    (by omega) hq hqm (by norm_num) i j hi hj D hw hp
  rw [← D5.S3.Estimation.TimeArrow.NativeReferenceCalibration.all_row_reference_sum
      S r (fun c => referenceParameter M q r c * (1 - referenceParameter M q r c)) i j hi hj] at hbound
  apply le_trans _ hbound
  have hh := mul_le_mul_of_nonneg_left hcard (show 0 ≤ (q : ℝ) / 2 by positivity)
  have hC : 0 ≤ Real.exp (-(2 : ℝ) ^ 2 / ((1 + r) / 2) - 1) *
      Real.exp (-(2 : ℝ) ^ 2 / ((1 - r) / 2) - 1) /
      (Real.sqrt ((3 / 2) * ((1 + r) / 2)) * Real.sqrt ((3 / 2) * ((1 - r) / 2)) * L) := by
    positivity
  have hmult := mul_le_mul_of_nonneg_right hh hC
  convert hmult using 1 <;> field_simp <;> ring

end
end D5.S3.Estimation.TimeArrow.NativeReferenceVarianceBounds
