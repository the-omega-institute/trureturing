/- GID: D5/S3/Arith/Robin/Lagarias/ThresholdPerturbation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Lagarias/ThresholdPerturbation
   mirror-E: none(waiver:lagarias-threshold-perturbation)
   anchors: []
   utility: none
   digest: The sharp Lagarias threshold perturbation preserves the Robin margin endpoint. -/

import D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import OmegaBuild.Commands

compile_only_with_mathlib

/-! The harmonic threshold as a vanishing perturbation of the Robin threshold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation

private abbrev E : ℝ := Real.exp Real.eulerMascheroniConstant

def threshold (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

def gap (n : ℕ) : ℝ :=
  threshold n / n - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))

def margin (n : ℕ) : ℝ :=
  (threshold n / n - (ArithmeticFunction.sigma 1 n : ℝ) / n) *
    Real.sqrt (Real.log (n : ℝ))

private lemma gap_bounds (n : ℕ) (hn : 1 < Real.log (n : ℝ)) :
    let x := Real.log (n : ℝ)
    let a := (harmonic n : ℝ) - x
    E * a / (1 + a / x) ≤ x * gap n ∧
    x * gap n ≤ E * a + (1 + E) * ((x ^ 2 + x) / n) := by
  let N : ℝ := n
  let x := Real.log N
  let H : ℝ := harmonic n
  let a := H - x
  let b := Real.exp H / N - E
  let q := Real.log H - Real.log x
  have hn0 : n ≠ 0 := by
    intro he
    simp [he] at hn
  have hN : 0 < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hx : 0 < x := lt_trans zero_lt_one hn
  have hgamma : Real.eulerMascheroniConstant < a := by
    simpa [a, H, x, N, Real.eulerMascheroniSeq', hn0] using
      Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have ha : 0 < a := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hH : 0 < H := by dsimp [a] at ha; linarith
  have hH1 : 1 < H := by dsimp [a] at ha; linarith
  have hHup : H ≤ x + 1 := by
    have hh := harmonic_le_one_add_log n
    change H ≤ 1 + x at hh
    linarith
  have hElower : E * N ≤ Real.exp H := by
    calc
      E * N = Real.exp (Real.eulerMascheroniConstant + x) := by
        rw [Real.exp_add, Real.exp_log hN]
      _ ≤ Real.exp H := Real.exp_le_exp.mpr (by dsimp [a] at hgamma; linarith)
  have hEupper : Real.exp H ≤ E * (N + 1) := by
    have hh := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
    change H - Real.log (N + 1) < Real.eulerMascheroniConstant at hh
    calc
      Real.exp H ≤ Real.exp (Real.eulerMascheroniConstant + Real.log (N + 1)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = E * (N + 1) := by rw [Real.exp_add, Real.exp_log (by positivity)]
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith [(le_div_iff₀ hN).mpr hElower]
  have hbup : b ≤ E / N := by
    dsimp [b]
    have hh := div_le_div_of_nonneg_right hEupper hN.le
    have heq : E * (N + 1) / N = E + E / N := by field_simp; ring
    linarith
  have hlogH : 0 ≤ Real.log H := (Real.log_pos hH1).le
  have hlogHup : Real.log H ≤ x + 1 :=
    (Real.log_le_sub_one_of_pos hH).trans (by linarith)
  have hqlo : 1 - x / H ≤ q := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hH hx)
    simpa [q, Real.log_div hH.ne' hx.ne', inv_div] using hh
  have hqup : q ≤ H / x - 1 := by
    simpa [q, Real.log_div hH.ne' hx.ne'] using
      Real.log_le_sub_one_of_pos (div_pos hH hx)
  have hid : x * gap n = x * H / N + x * b * Real.log H + E * x * q := by
    dsimp [gap, threshold, b, q, x, H, N, E]
    field_simp [hN.ne']
    ring
  have hloeq : E * a / (1 + a / x) = E * x * (1 - x / H) := by
    have hden : 1 + a / x = H / x := by
      dsimp [a]
      field_simp [hx.ne']
      ring
    rw [hden]
    dsimp [a]
    field_simp [hx.ne', hH.ne']
    ring
  have hulo : E * x * q ≤ E * a := by
    have hh := mul_le_mul_of_nonneg_left hqup (mul_pos (Real.exp_pos _) hx).le
    have heq : E * x * (H / x - 1) = E * a := by
      dsimp [a]
      field_simp [hx.ne']
      ring
    rwa [heq] at hh
  have herr : x * H / N + x * b * Real.log H ≤
      (1 + E) * ((x ^ 2 + x) / N) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHup hx.le) hN.le
    have hh' := mul_le_mul_of_nonneg_left
      (mul_le_mul hbup hlogHup hlogH (by positivity : 0 ≤ E / N)) hx.le
    nlinarith only [hh, hh']
  change E * a / (1 + a / x) ≤ x * gap n ∧
    x * gap n ≤ E * a + (1 + E) * ((x ^ 2 + x) / N)
  rw [hid]
  constructor
  · rw [hloeq]
    have hh := mul_le_mul_of_nonneg_left hqlo (mul_pos (Real.exp_pos _) hx).le
    have hr : 0 ≤ x * H / N := by positivity
    have hr' : 0 ≤ x * b * Real.log H := by positivity
    linarith
  · linarith

/-- The exact leading coefficient of the difference between the harmonic and
Robin thresholds, after division by the integer. -/
theorem threshold_asymptotic :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) * gap n) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * Real.eulerMascheroniConstant)) := by
  let x (n : ℕ) := Real.log (n : ℝ)
  let a (n : ℕ) := (harmonic n : ℝ) - x n
  have hx : Tendsto x atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : Tendsto a atTop (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hax : Tendsto (fun n => a n / x n) atTop (𝓝 0) := ha.div_atTop hx
  have hlo : Tendsto (fun n => E * a n / (1 + a n / x n)) atTop
      (𝓝 (E * Real.eulerMascheroniConstant)) := by
    have hd : Tendsto (fun n => 1 + a n / x n) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add hax
    simpa using (ha.const_mul E).div hd one_ne_zero
  have hp (k : ℕ) : Tendsto (fun n : ℕ => x n ^ k / (n : ℝ)) atTop (𝓝 0) := by
    simpa [x] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => (x n ^ 2 + x n) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [add_div] using (hp 2).add (by simpa using hp 1)
  have hup : Tendsto (fun n : ℕ => E * a n + (1 + E) *
      ((x n ^ 2 + x n) / (n : ℝ))) atTop (𝓝 (E * Real.eulerMascheroniConstant)) := by
    simpa using (ha.const_mul E).add (herr.const_mul (1 + E))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [hx.eventually_gt_atTop 1] with n hn
    exact (gap_bounds n hn).1
  · filter_upwards [hx.eventually_gt_atTop 1] with n hn
    exact (gap_bounds n hn).2

private lemma margin_difference :
    Tendsto (fun n : ℕ => margin n - Analytic.RHSharpAllIntegerMargin.T n)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := threshold_asymptotic.div_atTop (Real.tendsto_sqrt_atTop.comp hx)
  apply hs.congr'
  filter_upwards [hx.eventually_gt_atTop 0] with n hn
  have hs0 : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  calc
    Real.log (n : ℝ) * gap n / Real.sqrt (Real.log (n : ℝ)) =
        gap n * Real.sqrt (Real.log (n : ℝ)) := by
      apply (div_eq_iff₀ hs0.ne').mpr
      calc
        Real.log (n : ℝ) * gap n = gap n * Real.log (n : ℝ) := mul_comm _ _
        _ = gap n * Real.sqrt (Real.log (n : ℝ)) *
            Real.sqrt (Real.log (n : ℝ)) := by
          rw [mul_assoc, ← pow_two, hsq]
    _ = margin n - Analytic.RHSharpAllIntegerMargin.T n := by
      dsimp [margin, Analytic.RHSharpAllIntegerMargin.T, gap]
      ring

open D5.S3.Arith.GoldenResourceOptimalInteger (goldenResourceObjective)
open D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin (K)

/-- The Lagarias margin has the same sharp lower endpoint as the Robin
margin, attained arbitrarily late at the same original positive-price records. -/
theorem sharp_lagarias_margin (hRH : RiemannHypothesis) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E * K - ε < margin n) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m : ℕ, ∃ lambda : ℝ,
      N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧
      |margin m - E * K| < ε) ∧
    Filter.liminf margin atTop = E * K := by
  have hbase := Analytic.RHSharpAllIntegerMargin.all_integer_sharp_margin hRH
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop, |margin n - Analytic.RHSharpAllIntegerMargin.T n| < ε := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp margin_difference) ε hε
  have hlo (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop, E * K - ε < margin n := by
    obtain ⟨N, hN⟩ := hbase.1 (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop N, hsmall (ε / 2) (by positivity)] with n hn he
    have hb := (hN n hn).2
    have hd := (abs_lt.mp he).1
    linarith
  have hatt (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
      ∃ m : ℕ, ∃ lambda : ℝ, N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧
      |margin m - E * K| < ε := by
    obtain ⟨L, hL⟩ := eventually_atTop.mp (hsmall (ε / 2) (by positivity))
    obtain ⟨m, lambda, hm, hlambda, hm2, hr, _, ht⟩ :=
      hbase.2.1 (ε / 2) (by positivity) (max N L)
    refine ⟨m, lambda, (le_max_left _ _).trans hm, hlambda, hm2, hr, ?_⟩
    have hd := hL m ((le_max_right _ _).trans hm)
    have hh := abs_add_le (margin m - Analytic.RHSharpAllIntegerMargin.T m)
      (Analytic.RHSharpAllIntegerMargin.T m - E * K)
    rw [sub_add_sub_cancel] at hh
    linarith
  refine ⟨(fun ε hε => eventually_atTop.mp (hlo ε hε)), hatt, ?_⟩
  have hlower (b : ℝ) (hb : b < E * K) : ∀ᶠ n : ℕ in atTop, b ≤ margin n := by
    filter_upwards [hlo (E * K - b) (sub_pos.mpr hb)] with n hn
    linarith
  have hupper (b : ℝ) (hb : E * K < b) : ∃ᶠ n : ℕ in atTop, margin n ≤ b := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, _, hn, _, _, _, he⟩ := hatt (b - E * K) (sub_pos.mpr hb) N
    exact ⟨n, hn, by linarith [(abs_lt.mp he).2]⟩
  have hbounded : IsBoundedUnder (· ≥ ·) atTop margin :=
    isBoundedUnder_of_eventually_ge (hlower (E * K - 1) (by linarith))
  have hcobounded : IsCoboundedUnder (· ≥ ·) atTop margin :=
    IsCoboundedUnder.of_frequently_le (hupper (E * K + 1) (by linarith))
  exact le_antisymm ((liminf_le_iff' hcobounded hbounded).mpr hupper)
    ((le_liminf_iff' hcobounded hbounded).mpr hlower)

end D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation
