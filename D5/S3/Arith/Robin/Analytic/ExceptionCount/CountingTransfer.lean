/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/CountingTransfer
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/CountingTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform control of the logarithmic scale on dyadic counting intervals. -/

import D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer
open OmegaTailUpper OmegaTail Counting

private lemma scale_mono {x y : ℝ} (hx : exp (exp 1) ≤ x) (hxy : x ≤ y) :
    scale x ≤ scale y := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlx : exp 1 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hly : exp 1 ≤ log y := hlx.trans (log_le_log hx0 hxy)
  have h := log_div_self_antitoneOn hlx hly (log_le_log hx0 hxy)
  have hp : 0 < log (log y) / log y :=
    div_pos (log_pos ((one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hly))
      ((exp_pos _).trans_le hly)
  simpa only [one_div_div, scale] using one_div_le_one_div_of_le hp h

private lemma scale_dilation (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => scale (c * x) / scale x) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℝ => log (c * x) / log x) atTop (𝓝 1) := by
    have h := (tendsto_log_atTop.const_div_atTop (log c)).add
      (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [log_mul hc.ne' (by linarith : x ≠ 0), add_div,
      div_self (log_pos hx).ne']
  have hloglog : Tendsto (fun x : ℝ => log (log (c * x)) / log (log x))
      atTop (𝓝 1) := by
    have hsmall : Tendsto (fun x : ℝ =>
        log (log (c * x) / log x) / log (log x)) atTop (𝓝 0) :=
      (hlog.log (by norm_num : (1 : ℝ) ≠ 0)).div_atTop
        (tendsto_log_atTop.comp tendsto_log_atTop)
    have h := hsmall.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (exp 1),
      (tendsto_id.const_mul_atTop hc).eventually_gt_atTop (1 : ℝ)] with x hx hcx
    change 1 < c * x at hcx
    have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans hx
    have hlx1 : 1 < log x := (lt_log_iff_exp_lt ((exp_pos _).trans hx)).mpr hx
    rw [log_div (log_pos hcx).ne' (log_pos hx1).ne', sub_div,
      div_self (log_pos hlx1).ne']
    ring
  convert hlog.div hloglog (by norm_num : (1 : ℝ) ≠ 0) using 1
  · ext x
    dsimp [scale]
    ring
  · norm_num

private lemma dyadic_endpoint {N : ℕ} (hN : 1 < N) :
    (2 : ℝ) ^ Nat.clog 2 N < 2 * N := by
  have hj : 0 < Nat.clog 2 N := Nat.clog_pos (by norm_num) hN
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hN
  have hp' : (2 : ℝ) ^ (Nat.clog 2 N - 1) < N := by
    exact_mod_cast hp
  have he : Nat.clog 2 N = Nat.clog 2 N - 1 + 1 := by omega
  rw [he, pow_succ]
  nlinarith

/-- A finite dyadic transfer with an explicit logarithmic prefactor. -/
private lemma finite_count_transfer (E : ℕ → Prop) [DecidablePred E]
    (J : ℕ) (lambda A x : ℝ)
    (hx : exp (exp 1) ≤ x) (hA : 0 ≤ A)
    (hJ : exp (exp 1) ≤ (2 : ℝ) ^ J)
    (hlocal : ∀ j : ℕ, J < j → j ≤ Nat.clog 2 ⌊x⌋₊ →
      ∀ n : ℕ, (2 : ℝ) ^ j / 2 < n → (n : ℝ) ≤ (2 : ℝ) ^ j → E n →
        threshold lambda ((2 : ℝ) ^ j) <
          (ArithmeticFunction.cardDistinctFactors n : ℝ))
    (htail : ∀ j : ℕ, J < j → j ≤ Nat.clog 2 ⌊x⌋₊ →
      (tailCount lambda ((2 : ℝ) ^ j) : ℝ) ≤
        exp (A * scale ((2 : ℝ) ^ j))) :
    (((Icc 1 ⌊x⌋₊).filter E).card : ℝ) ≤
      ((2 : ℝ) ^ J + log (2 * x) / log 2 + 1) * exp (A * scale (2 * x)) := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hx2 : (2 : ℝ) ≤ x := by
    have he : (2 : ℝ) < exp (exp 1) := by
      have h1 := add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      have h2 := add_one_lt_exp (ne_of_gt (exp_pos (1 : ℝ)))
      linarith
    exact he.le.trans hx
  have hN : 1 < ⌊x⌋₊ := by
    have : (2 : ℕ) ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr hx2
    omega
  have hcap : (2 : ℝ) ^ Nat.clog 2 ⌊x⌋₊ ≤ 2 * x :=
    (dyadic_endpoint hN).le.trans (by gcongr; exact Nat.floor_le hx0.le)
  have hjcap : (Nat.clog 2 ⌊x⌋₊ : ℝ) ≤ log (2 * x) / log 2 := by
    have hl := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hcap
    rw [log_pow] at hl
    exact (le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl
  have hscale : 0 ≤ scale (2 * x) := by
    apply (scale_pos _).le
    have h1 : exp 1 < exp (exp 1) := exp_lt_exp.mpr (one_lt_exp_iff.mpr (by norm_num))
    linarith
  have hexp : 1 ≤ exp (A * scale (2 * x)) := one_le_exp (mul_nonneg hA hscale)
  have hsum : (∑ j ∈ Icc (J + 1) (Nat.clog 2 ⌊x⌋₊),
      (tailCount lambda ((2 : ℝ) ^ j) : ℝ)) ≤
      (Nat.clog 2 ⌊x⌋₊ + 1 : ℕ) * exp (A * scale (2 * x)) := by
    calc
      _ ≤ ∑ _j ∈ Icc (J + 1) (Nat.clog 2 ⌊x⌋₊), exp (A * scale (2 * x)) := by
        apply sum_le_sum
        intro j hj
        have hj' := mem_Icc.mp hj
        apply (htail j (by omega) hj'.2).trans
        apply exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hA
        apply scale_mono
        · exact hJ.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
        · exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj'.2).trans hcap
      _ ≤ (Nat.clog 2 ⌊x⌋₊ + 1 : ℕ) * exp (A * scale (2 * x)) := by
        simp only [sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (show (Icc (J + 1) (Nat.clog 2 ⌊x⌋₊)).card ≤
          Nat.clog 2 ⌊x⌋₊ + 1 by simp; omega)
  have hcount := dyadic_cover_count E ⌊x⌋₊ J lambda hlocal
  have hcount' : (((Icc 1 ⌊x⌋₊).filter E).card : ℝ) ≤
      (2 : ℝ) ^ J + ∑ j ∈ Icc (J + 1) (Nat.clog 2 ⌊x⌋₊),
        (tailCount lambda ((2 : ℝ) ^ j) : ℝ) := by exact_mod_cast hcount
  calc
    _ ≤ (2 : ℝ) ^ J + (Nat.clog 2 ⌊x⌋₊ + 1 : ℕ) * exp (A * scale (2 * x)) :=
      hcount'.trans (add_le_add_right hsum _)
    _ ≤ ((2 : ℝ) ^ J + log (2 * x) / log 2 + 1) * exp (A * scale (2 * x)) := by
      have hp : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ J * exp (A * scale (2 * x)) := by
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) J]
      push_cast
      nlinarith [exp_pos (A * scale (2 * x))]

private lemma log_prefactor_negligible (D : ℝ) :
    Tendsto (fun x : ℝ =>
      log (D + log (2 * x) / log 2 + 1) / scale x) atTop (𝓝 0) := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hratio : Tendsto (fun x : ℝ =>
      (D + log (2 * x) / log 2 + 1) / log x) atTop (𝓝 (1 / log 2)) := by
    have h := (tendsto_log_atTop.const_div_atTop (D + 2)).add
      (tendsto_const_nhds (x := 1 / log (2 : ℝ)) (f := atTop))
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : x ≠ 0)]
    field_simp [(log_pos hx).ne', hlog2.ne']
    <;> ring
  have hsmall := (hratio.log (by positivity : (1 / log (2 : ℝ)) ≠ 0)).div_atTop
    scale_tendsto
  have h := hsmall.add OmegaTail.Selection.loglog_div_scale
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hratio.eventually_const_lt (by positivity : (0 : ℝ) < 1 / log 2)] with x hx hp
  rw [← add_div, ← log_mul (ne_of_gt hp) (log_pos hx).ne']
  congr 2
  field_simp [(log_pos hx).ne', hlog2.ne']

/-- Local exclusion below every sufficiently slightly relaxed distinct-prime
threshold yields the sharp global exponential upper bound. -/
theorem count_from_local_exclusion (E : ℕ → Prop) [DecidablePred E]
    (hlocal : ∀ eta : ℝ, 0 < eta → ∀ᶠ t : ℝ in atTop,
      ∀ n : ℕ, t / 2 < n → (n : ℝ) ≤ t → E n →
        threshold (-eta) t < (ArithmeticFunction.cardDistinctFactors n : ℝ))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop, (((Icc 1 ⌊x⌋₊).filter E).card : ℝ) ≤
      exp ((C0 + epsilon) * scale x) := by
  obtain ⟨eta, heta, htail⟩ := relaxed_tail_upper (show 0 < epsilon / 4 by positivity)
  obtain ⟨B, hB⟩ := eventually_atTop.mp ((hlocal eta heta).and htail)
  have hpow : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (hpow.eventually_ge_atTop (max B (exp (exp 1))))
  have hJB : B ≤ (2 : ℝ) ^ J := (le_max_left _ _).trans (hJ J le_rfl)
  have hJscale : exp (exp 1) ≤ (2 : ℝ) ^ J :=
    (le_max_right _ _).trans (hJ J le_rfl)
  let A : ℝ := C0 + epsilon / 4
  have hA : 0 < A := by dsimp [A]; linarith [constant_gt_one]
  have hlimit : Tendsto (fun x : ℝ =>
      log ((2 : ℝ) ^ J + log (2 * x) / log 2 + 1) / scale x +
        A * (scale (2 * x) / scale x)) atTop (𝓝 A) := by
    simpa only [mul_one, zero_add] using
      (log_prefactor_negligible ((2 : ℝ) ^ J)).add
        ((scale_dilation 2 (by norm_num)).const_mul A)
  filter_upwards [eventually_ge_atTop (exp (exp 1)),
    hlimit.eventually_lt_const (show A < C0 + epsilon by dsimp [A]; linarith)]
    with x hx hsmall
  have hbound := finite_count_transfer E J (-eta) A x hx hA.le hJscale
    (fun j hj _ n hnlo hnhi hE =>
      (hB ((2 : ℝ) ^ j) (hJB.trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj.le))).1 n hnlo hnhi hE)
    (fun j hj _ =>
      (hB ((2 : ℝ) ^ j) (hJB.trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj.le))).2)
  apply hbound.trans
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (exp_pos (1 : ℝ))).trans_le hx
  have hcoeff : 0 < (2 : ℝ) ^ J + log (2 * x) / log 2 + 1 := by
    have h2x : 1 < 2 * x := by linarith
    have hlog2x : 0 < log (2 * x) := log_pos h2x
    have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    positivity
  have hscale : 0 < scale x := by
    apply scale_pos
    have h1 : exp 1 < exp (exp 1) := exp_lt_exp.mpr (one_lt_exp_iff.mpr (by norm_num))
    exact h1.trans_le hx
  rw [← exp_log hcoeff, ← exp_add]
  apply exp_le_exp.mpr
  have hsmall' : log ((2 : ℝ) ^ J + log (2 * x) / log 2 + 1) +
      A * scale (2 * x) < (C0 + epsilon) * scale x := by
    apply (div_lt_iff₀ hscale).mp
    convert hsmall using 1 <;> field_simp <;> ring
  exact hsmall'.le

end D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer
