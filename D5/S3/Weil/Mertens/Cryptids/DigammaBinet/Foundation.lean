/- GID: D5/S3/Weil/Mertens/Cryptids/DigammaBinet/Foundation
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/DigammaBinet/Foundation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids DigammaBinet analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/DigammaBinet.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv

/-! Original DigammaBinet analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.DigammaBinet


open Complex Finset Filter MeasureTheory Set
open scoped Real Topology Interval ArithmeticFunction.vonMangoldt LSeries.notation

/-- For `x > 0`, `(x : ℂ) ≠ -(m : ℂ)` for all `m : ℕ`. -/
theorem ofReal_ne_neg_natCast_of_pos {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- For `s : ℂ` with `0 < s.re`, `s ≠ -(m : ℂ)` for all `m : ℕ`. -/
theorem ne_neg_natCast_of_re_pos {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    s ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- For `x : ℝ` with `0 < x`, `deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ)`. -/
theorem deriv_Gamma_ofReal_eq {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hC : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (ofReal_ne_neg_natCast_of_pos hx)
  have hR : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h1 : HasDerivAt (fun y : ℝ ↦ Complex.Gamma (y : ℂ)) (deriv Complex.Gamma (x : ℂ)) x :=
    hC.hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ ↦ Complex.Gamma (y : ℂ)) ((deriv Real.Gamma x : ℝ) : ℂ) x := by
    rw [show (fun y : ℝ ↦ Complex.Gamma (y : ℂ)) = fun y : ℝ ↦ (Real.Gamma y : ℂ) from
      funext Complex.Gamma_ofReal]
    exact hR.hasDerivAt.ofReal_comp
  exact h1.unique h2

/-- For `x : ℝ` with `0 < x`,
`Complex.digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ)`. -/
theorem digamma_ofReal_eq_deriv_log_Gamma {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  have hR : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  rw [Complex.digamma_def, logDeriv_apply, deriv_Gamma_ofReal_eq hx, Complex.Gamma_ofReal,
    Function.comp_def, deriv.log hR hpos.ne', Complex.ofReal_div]

/-- For `x : ℝ` with `0 < x`, `(Complex.digamma (x : ℂ)).re = deriv (Real.log ∘ Real.Gamma) x`. -/
theorem digamma_ofReal_re {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).re = deriv (Real.log ∘ Real.Gamma) x := by
  rw [digamma_ofReal_eq_deriv_log_Gamma hx, Complex.ofReal_re]

/-- **Bohr–Mollerup Convexity Sandwich for `Complex.digamma (x + 1)`**:
For all real `x > 0`,
$$\log x \le \operatorname{Re}\psi(x + 1) \le \log(x + 1).$$ -/
theorem digamma_add_one_re_sandwich {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ (Complex.digamma ((x : ℂ) + 1)).re ∧
      (Complex.digamma ((x : ℂ) + 1)).re ≤ Real.log (x + 1) := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (y : ℝ) (hy : 0 < y) : f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine (Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_) <;>
      exact fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hx1_cast : ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hx1_cast, digamma_ofReal_re (by positivity)]
  constructor
  · refine (le_of_eq ?_).trans <|
      hc.slope_le_deriv (mem_Ioi.mpr hx) (by positivity : (0 : ℝ) < x + 1)
        (by linarith) (hder (by positivity))
    rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one, h_rec x hx,
      add_sub_cancel_left]
  · refine (hc.deriv_le_slope (by positivity : (0 : ℝ) < x + 1)
      (by positivity : (0 : ℝ) < x + 2) (by linarith) (hder (by positivity))).trans (le_of_eq ?_)
    rw [slope_def_field, show x + 2 - (x + 1) = (1 : ℝ) by ring, div_one,
      show x + 2 = (x + 1) + 1 by ring, h_rec (x + 1) (by positivity), add_sub_cancel_left]

/-- **Bohr–Mollerup Convexity Sandwich for `Complex.digamma x`**:
For all real `x > 0`,
$$\log x - \frac{1}{x} \le \operatorname{Re}\psi(x) \le \log x.$$ -/
theorem digamma_ofReal_re_sandwich {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / x ≤ (Complex.digamma (x : ℂ)).re ∧
      (Complex.digamma (x : ℂ)).re ≤ Real.log x := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec : f (x + 1) = f x + Real.log x := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hx.ne',
      Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm]
  have hder : DifferentiableAt ℝ f x := by
    refine (Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_) <;>
      exact fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h_step := Complex.digamma_apply_add_one (x : ℂ) (ofReal_ne_neg_natCast_of_pos hx)
  have h_re_step : (Complex.digamma ((x : ℂ) + 1)).re = (Complex.digamma (x : ℂ)).re + 1 / x := by
    rw [h_step, add_re, inv_re, normSq_ofReal, ofReal_re, div_self_mul_self', one_div]
  have h_lb := (digamma_add_one_re_sandwich hx).1
  constructor
  · linarith
  · rw [digamma_ofReal_re hx]
    refine (hc.deriv_le_slope (mem_Ioi.mpr hx) (by positivity : (0 : ℝ) < x + 1)
      (by linarith) hder).trans (le_of_eq ?_)
    rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one, h_rec, add_sub_cancel_left]

/-- For all real `x > 0`, `‖Complex.digamma (x : ℂ) - Complex.log (x : ℂ)‖ ≤ 1 / x`. -/
theorem norm_digamma_ofReal_sub_log_le {x : ℝ} (hx : 0 < x) :
    ‖Complex.digamma (x : ℂ) - Complex.log (x : ℂ)‖ ≤ 1 / x := by
  have h_eq :
      Complex.digamma (x : ℂ) - Complex.log (x : ℂ) =
        ((deriv (Real.log ∘ Real.Gamma) x - Real.log x : ℝ) : ℂ) := by
    rw [digamma_ofReal_eq_deriv_log_Gamma hx, ← Complex.ofReal_log hx.le, ← Complex.ofReal_sub]
  rw [h_eq, Complex.norm_real, Real.norm_eq_abs, ← digamma_ofReal_re hx, abs_le]
  have h_sand := digamma_ofReal_re_sandwich hx
  have hx_inv : 0 ≤ 1 / x := by positivity
  constructor <;> linarith

/-- **Asymptotic Vanishing of `ψ(x + n) - log(x + n)` as `n → ∞`**:
For all real `x > 0`,
$$\lim_{n \to \infty} \bigl(\psi(x + n) - \log(x + n)\bigr) = 0.$$ -/
theorem tendsto_digamma_add_nat_sub_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ ↦ Complex.digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_le : ∀ n : ℕ,
      ‖Complex.digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n)‖ ≤ 1 / (x + (n : ℝ)) := by
    intro n
    have hxn_pos : 0 < x + (n : ℝ) := by positivity
    have h_cast : (x : ℂ) + (n : ℂ) = ((x + n : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast]
    exact norm_digamma_ofReal_sub_log_le hxn_pos
  have h_lim : Tendsto (fun n : ℕ ↦ 1 / (x + (n : ℝ))) atTop (𝓝 0) := by
    have h_tendsto : Tendsto (fun n : ℕ ↦ x + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h_tendsto
  exact squeeze_zero (fun _ ↦ norm_nonneg _) h_le h_lim

/-- The sawtooth / first periodic Bernoulli function `B₁(t - ⌊t⌋₊) = t - ⌊t⌋₊ - 1 / 2`. -/
noncomputable def sawtoothB1 (t : ℝ) : ℝ :=
  t - ⌊t⌋₊ - 1 / 2

/-- For all `t ≥ 0`, `|sawtoothB1 t| ≤ 1 / 2`. -/
theorem abs_sawtoothB1_le_half {t : ℝ} (ht : 0 ≤ t) :
    |sawtoothB1 t| ≤ 1 / 2 := by
  unfold sawtoothB1
  have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have h2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  rw [abs_le]
  constructor <;> linarith

/-- Measurability of `sawtoothB1`. -/
theorem measurable_sawtoothB1 : Measurable sawtoothB1 := by
  unfold sawtoothB1
  exact (measurable_id.sub
    (measurable_from_top.comp Nat.floor_mono.measurable)).sub measurable_const

/-- The Euler–Maclaurin / Binet integrand `(t - ⌊t⌋₊ - 1 / 2 : ℂ) / (s + t) ^ 2`. -/
noncomputable def binetIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) - ⌊t⌋₊ - 1 / 2) / (s + t) ^ 2

theorem binetIntegrand_eq_sawtoothB1 (s : ℂ) (t : ℝ) :
    binetIntegrand s t = (sawtoothB1 t : ℂ) / (s + t) ^ 2 := by
  unfold binetIntegrand sawtoothB1
  push_cast
  rfl

/-- For `s : ℂ` with `0 < s.re` and `t ≥ 0`, `s + t ∈ Complex.slitPlane`. -/
theorem add_ofReal_mem_slitPlane {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    s + (t : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [add_re, ofReal_re]
  linarith

/-- For `s : ℂ` with `0 < s.re` and `t ≥ 0`, `s.re + t ≤ ‖s + t‖`. -/
theorem re_add_le_norm_add_ofReal {s : ℂ} {t : ℝ} :
    s.re + t ≤ ‖s + (t : ℂ)‖ := by
  have h : (s + (t : ℂ)).re ≤ ‖s + (t : ℂ)‖ := Complex.re_le_norm (s + (t : ℂ))
  simpa using h

/-- For `s : ℂ` with `0 < s.re` and `t ≥ 0`, `s + (t : ℂ) ≠ 0`. -/
theorem add_ofReal_ne_zero {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    s + (t : ℂ) ≠ 0 :=
  Complex.slitPlane_ne_zero (add_ofReal_mem_slitPlane hs ht)

/-- Pointwise norm bound on `binetIntegrand s t` for `0 < s.re` and `0 ≤ t`:
`‖binetIntegrand s t‖ ≤ (1 / 2) / (s.re + t) ^ 2`. -/
theorem norm_binetIntegrand_le {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖binetIntegrand s t‖ ≤ (1 / 2) / (s.re + t) ^ 2 := by
  rw [binetIntegrand_eq_sawtoothB1, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  have hpos : 0 < s.re + t := by linarith
  have h_norm : (s.re + t) ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ hpos.le re_add_le_norm_add_ofReal 2
  exact div_le_div₀ (by norm_num) (abs_sawtoothB1_le_half ht) (sq_pos_of_pos hpos) h_norm

/-- Exact improper integral `∫ t in Ioi (0 : ℝ), 1 / (a + t) ^ 2 = 1 / a` for `a > 0`. -/
theorem integral_Ioi_one_div_add_sq {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, 1 / (a + t) ^ 2) = 1 / a := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ ↦ -(a + u)⁻¹) (1 / (a + t) ^ 2) t := by
    intro t ht
    have hat : a + t ≠ 0 := by linarith [mem_Ici.mp ht]
    have hd := ((hasDerivAt_id t).const_add a).inv hat |>.neg
    refine hd.congr_deriv ?_
    simp only [id_eq]
    ring
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + t) ^ 2 := fun t _ ↦ by positivity
  have htend : Tendsto (fun u : ℝ ↦ -(a + u)⁻¹) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -0 by ring]
    exact (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a tendsto_id)).neg
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend]
  ring

/-- Integrability of `t ↦ 1 / (a + t) ^ 2` on `Ioi (0 : ℝ)` for `a > 0`. -/
theorem integrableOn_Ioi_one_div_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ 1 / (a + t) ^ 2) (Ioi 0) := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ ↦ -(a + u)⁻¹) (1 / (a + t) ^ 2) t := by
    intro t ht
    have hat : a + t ≠ 0 := by linarith [mem_Ici.mp ht]
    have hd := ((hasDerivAt_id t).const_add a).inv hat |>.neg
    refine hd.congr_deriv ?_
    simp only [id_eq]
    ring
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + t) ^ 2 := fun t _ ↦ by positivity
  have htend : Tendsto (fun u : ℝ ↦ -(a + u)⁻¹) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -0 by ring]
    exact (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a tendsto_id)).neg
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend

/-- Measurability of `binetIntegrand s`. -/
theorem measurable_binetIntegrand (s : ℂ) : Measurable (binetIntegrand s) := by
  rw [funext (binetIntegrand_eq_sawtoothB1 s)]
  refine (Complex.measurable_ofReal.comp measurable_sawtoothB1).div ?_
  exact ((measurable_const.add Complex.measurable_ofReal).pow_const 2)

/-- `binetIntegrand s` is `IntegrableOn` `Ioi (0 : ℝ)` for every `s : ℂ` with `0 < s.re`. -/
theorem integrableOn_Ioi_binetIntegrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (binetIntegrand s) (Ioi 0) := by
  have h_dom : IntegrableOn (fun t : ℝ ↦ (1 / 2) * (1 / (s.re + t) ^ 2)) (Ioi 0) :=
    (integrableOn_Ioi_one_div_add_sq hs).const_mul (1 / 2)
  refine h_dom.mono' (measurable_binetIntegrand s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (norm_binetIntegrand_le hs (mem_Ioi.mp ht).le).trans_eq (by ring)

/-- For every `s : ℂ` with `0 < s.re` and every `a b : ℝ` with `0 ≤ a ≤ b`, `binetIntegrand s`
is `IntervalIntegrable` on `a..b`. -/
theorem intervalIntegrable_binetIntegrand {s : ℂ} (hs : 0 < s.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (binetIntegrand s) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine (integrableOn_Ioi_binetIntegrand hs).mono_set ?_
  intro t ht
  exact mem_Ioi.mpr (ha.trans_lt ht.1)

/-- The 1D antiderivative on $[k, k + 1]$ for the Euler–Maclaurin formula:
$$\Phi_{\text{EM}}(s, k, t) := \log(s + t) - \frac{t - k - 1/2}{s + t}.$$ -/
noncomputable def eulerMaclaurinAntideriv (s : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  Complex.log (s + t) - ((t : ℂ) - k - 1 / 2) / (s + t)

/-- Exact derivative of `eulerMaclaurinAntideriv s k` for `0 < s.re` and `0 ≤ t`:
`HasDerivAt (eulerMaclaurinAntideriv s k) (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) t`. -/
theorem hasDerivAt_eulerMaclaurinAntideriv {s : ℂ} (hs : 0 < s.re) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (eulerMaclaurinAntideriv s k) (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) t := by
  unfold eulerMaclaurinAntideriv
  have h_slit : s + (t : ℂ) ∈ Complex.slitPlane := add_ofReal_mem_slitPlane hs ht
  have h_ne : s + (t : ℂ) ≠ 0 := Complex.slitPlane_ne_zero h_slit
  have hd_ofReal : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hd_st : HasDerivAt (fun u : ℝ ↦ s + (u : ℂ)) 1 t := by
    simpa using hd_ofReal.const_add s
  have hd_log : HasDerivAt (fun u : ℝ ↦ Complex.log (s + u)) (1 / (s + t)) t :=
    hd_st.clog_real h_slit
  have hd_num : HasDerivAt (fun u : ℝ ↦ (u : ℂ) - k - 1 / 2) 1 t := by
    simpa using (hd_ofReal.sub_const (k : ℂ)).sub_const (1 / 2 : ℂ)
  have hd_quot := hd_num.div hd_st h_ne
  refine (hd_log.sub hd_quot).congr_deriv ?_
  rw [div_sub_div _ _ h_ne (pow_ne_zero 2 h_ne)]
  have h_num_eq :
      1 * (s + (t : ℂ)) ^ 2 - (s + (t : ℂ)) * (1 * (s + (t : ℂ)) - ((t : ℂ) - k - 1 / 2) * 1) =
        ((t : ℂ) - k - 1 / 2) * (s + (t : ℂ)) := by
    ring
  rw [h_num_eq]
  have h_pow : (s + (t : ℂ)) * (s + (t : ℂ)) ^ 2 = (s + (t : ℂ)) ^ 2 * (s + (t : ℂ)) := by ring
  rw [h_pow, mul_div_mul_right _ _ h_ne]

/-- **Unit-Interval Euler–Maclaurin Identity**:
For `0 < s.re` and `k : ℕ`,
$$\int_k^{k+1} \frac{t - k - 1/2}{(s + t)^2} \, dt
  = \log(s + k + 1) - \log(s + k) - \frac{1}{2(s + k + 1)} - \frac{1}{2(s + k)}.$$ -/
theorem intervalIntegral_eulerMaclaurin_unit {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2)) =
      Complex.log (s + k + 1) - Complex.log (s + k) -
        1 / (2 * (s + k + 1)) - 1 / (2 * (s + k)) := by
  have hk_le : (k : ℝ) ≤ k + 1 := by linarith
  have hderiv : ∀ t ∈ Set.uIcc (k : ℝ) (k + 1 : ℝ),
      HasDerivAt (eulerMaclaurinAntideriv s k) (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hk_le] at ht
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1
    exact hasDerivAt_eulerMaclaurinAntideriv hs k ht_nonneg
  have hint : IntervalIntegrable (fun t : ℝ ↦ (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2))
      volume (k : ℝ) (k + 1 : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hk_le]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1
    have h_ne : (s + (t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (add_ofReal_ne_zero hs ht_nonneg)
    refine ContinuousAt.div ?_ ?_ h_ne
    · fun_prop
    · fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold eulerMaclaurinAntideriv
  push_cast
  have h1 : s + ((k : ℂ) + 1) = s + (k : ℂ) + 1 := by ring
  have h2 : (k : ℂ) + 1 - (k : ℂ) - 1 / 2 = 1 / 2 := by ring
  have h3 : (k : ℂ) - (k : ℂ) - 1 / 2 = -(1 / 2) := by ring
  rw [h1, h2, h3]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Replacing `k` by `⌊t⌋₊` on `(k : ℝ)..(k + 1 : ℝ)` in `intervalIntegral_eulerMaclaurin_unit`,
written in telescoping form with `H(z) := log z - 1 / (2 * z)`. -/
theorem intervalIntegral_binetIntegrand_unit {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), binetIntegrand s t) =
      (Complex.log (s + (k + 1 : ℕ)) - 1 / (2 * (s + (k + 1 : ℕ)))) -
        (Complex.log (s + (k : ℕ)) - 1 / (2 * (s + (k : ℕ)))) -
        (s + (k : ℕ))⁻¹ := by
  have hk_le : (k : ℝ) ≤ k + 1 := by linarith
  have h_congr :
      (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), binetIntegrand s t) =
        ∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hk_le fun t ht ↦ ?_
    unfold binetIntegrand
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1.le
    have h_floor : ⌊t⌋₊ = k := Nat.floor_eq_iff ht_nonneg |>.mpr ⟨ht.1.le, ht.2⟩
    rw [h_floor]
  rw [h_congr, intervalIntegral_eulerMaclaurin_unit hs k]
  push_cast
  have h1 : s + ((k : ℂ) + 1) = s + (k : ℂ) + 1 := by ring
  rw [h1]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **Telescoped Finite Euler–Maclaurin Identity on `[0, n]`**:
For all `s : ℂ` with `0 < s.re` and all `n : ℕ`,
$$\int_0^n \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt
  = \log(s + n) - \log s + \frac{1}{2s} - \frac{1}{2(s + n)}
    - \sum_{k \in \operatorname{range} n} (s + k)^{-1}.$$ -/
theorem intervalIntegral_binetIntegrand_range {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand s t) =
      Complex.log (s + n) - Complex.log s + 1 / (2 * s) - 1 / (2 * (s + n)) -
        ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
  have h_adj :
      (∑ k ∈ Finset.range n, ∫ t : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), binetIntegrand s t) =
        ∫ t : ℝ in ((0 : ℕ) : ℝ)..(n : ℝ), binetIntegrand s t := by
    refine intervalIntegral.sum_integral_adjacent_intervals fun k _ ↦ ?_
    push_cast
    exact intervalIntegrable_binetIntegrand hs (Nat.cast_nonneg k) (by linarith)
  simp only [Nat.cast_zero] at h_adj
  rw [← h_adj]
  have h_sum_eq :
      (∑ k ∈ Finset.range n, ∫ t : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), binetIntegrand s t) =
        ∑ k ∈ Finset.range n,
          (((Complex.log (s + (k + 1 : ℕ)) - 1 / (2 * (s + (k + 1 : ℕ)))) -
              (Complex.log (s + (k : ℕ)) - 1 / (2 * (s + (k : ℕ))))) -
            (s + (k : ℕ))⁻¹) := by
    refine sum_congr rfl fun k _ ↦ ?_
    push_cast
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegral_binetIntegrand_unit hs k
  rw [h_sum_eq, sum_sub_distrib,
    sum_range_sub (fun k : ℕ ↦ Complex.log (s + (k : ℕ)) - 1 / (2 * (s + (k : ℕ)))) n]
  simp only [Nat.cast_zero, add_zero]
  ring

/-- **Finite Euler–Maclaurin Formula for `Complex.digamma s`**:
For all `s : ℂ` with `0 < s.re` and all `n : ℕ`,
$$\psi(s) = \log s - \frac{1}{2s} + \int_0^n \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt
  + \psi(s + n) - \log(s + n) + \frac{1}{2(s + n)}.$$ -/
theorem digamma_eq_log_sub_half_inv_sub_intervalIntegral_add_rem {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Complex.digamma s =
      Complex.log s - 1 / (2 * s) + (∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand s t) +
        (Complex.digamma (s + n) - Complex.log (s + n)) + 1 / (2 * (s + n)) := by
  have h_rec := Complex.digamma_apply_add_nat (ne_neg_natCast_of_re_pos hs) n
  have h_int := intervalIntegral_binetIntegrand_range hs n
  linear_combination -h_rec - h_int

/-- **Euler–Maclaurin / Binet Integral Representation for Real `x > 0`**:
For all real `x > 0`,
$$\psi(x) = \log x - \frac{1}{2x}
  + \int_{t \in \operatorname{Ioi} 0} \frac{t - \lfloor t \rfloor - 1/2}{(x + t)^2} \, dt.$$ -/
theorem digamma_ofReal_eq_eulerMaclaurin {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) =
      Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)) +
        ∫ t : ℝ in Ioi 0, binetIntegrand (x : ℂ) t := by
  have hx_re : 0 < (x : ℂ).re := by simpa using hx
  have h_int_tendsto :
      Tendsto (fun n : ℕ ↦ ∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand (x : ℂ) t)
        atTop (𝓝 (∫ t : ℝ in Ioi 0, binetIntegrand (x : ℂ) t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_Ioi_binetIntegrand hx_re) tendsto_natCast_atTop_atTop
  have h_rem1 :
      Tendsto (fun n : ℕ ↦ Complex.digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n))
        atTop (𝓝 0) :=
    tendsto_digamma_add_nat_sub_log hx
  have h_rem2 : Tendsto (fun n : ℕ ↦ (1 : ℂ) / (2 * ((x : ℂ) + n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_le : ∀ n : ℕ, ‖(1 : ℂ) / (2 * ((x : ℂ) + n))‖ ≤ 1 / (2 * (x + (n : ℝ))) := by
      intro n
      have hxn_pos : 0 < x + (n : ℝ) := by positivity
      have h_norm : x + (n : ℝ) ≤ ‖(x : ℂ) + (n : ℂ)‖ := by
        simpa using re_add_le_norm_add_ofReal (s := (x : ℂ)) (t := (n : ℝ))
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h_lim : Tendsto (fun n : ℕ ↦ 1 / (2 * (x + (n : ℝ)))) atTop (𝓝 0) := by
      have h_tend : Tendsto (fun n : ℕ ↦ 2 * (x + (n : ℝ))) atTop atTop :=
        (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop).const_mul_atTop
          (by norm_num)
      simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h_tend
    exact squeeze_zero (fun _ ↦ norm_nonneg _) h_le h_lim
  have h_c :
      Tendsto (fun _ : ℕ ↦ Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)))
        atTop (𝓝 (Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)))) :=
    tendsto_const_nhds
  have h_rhs := ((h_c.add h_int_tendsto).add h_rem1).add h_rem2
  simp only [add_zero] at h_rhs
  have h_const :
      Tendsto (fun _ : ℕ ↦ Complex.digamma (x : ℂ)) atTop (𝓝 (Complex.digamma (x : ℂ))) :=
    tendsto_const_nhds
  refine tendsto_nhds_unique h_const (h_rhs.congr fun n ↦ ?_)
  exact (digamma_eq_log_sub_half_inv_sub_intervalIntegral_add_rem hx_re n).symm

/-- Convexity of the open right half-plane `{s : ℂ | 0 < s.re}`. -/
theorem convex_rightHalfPlane : Convex ℝ {s : ℂ | 0 < s.re} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
  rcases lt_or_eq_of_le ha with ha' | rfl
  · have : 0 < a * x.re := mul_pos ha' hx
    have : 0 ≤ b * y.re := mul_nonneg hb hy.le
    linarith
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy

/-- Complex differentiability of `s ↦ ∫ t in Ioi 0, binetIntegrand s t` on `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_integral_binetIntegrand :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t : ℝ in Ioi 0, binetIntegrand s t)
      {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  simp only [mem_ofPred_eq] at hs₀
  set c : ℝ := s₀.re / 2
  have hc : 0 < c := half_pos hs₀
  let V : Set ℂ := {z : ℂ | c < z.re}
  have hV_open : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hs₀_V : s₀ ∈ V := by simp [V, c, half_lt_self hs₀]
  have hV_nhds : V ∈ 𝓝 s₀ := hV_open.mem_nhds hs₀_V
  let F : ℂ → ℝ → ℂ := binetIntegrand
  let F' : ℂ → ℝ → ℂ := fun z t ↦ -2 * (sawtoothB1 t : ℂ) / (z + t) ^ 3
  let bound : ℝ → ℝ := fun t ↦ (1 / c) * (1 / (c + t) ^ 2)
  have hF'_meas : ∀ z : ℂ, Measurable (F' z) := by
    intro z
    refine (measurable_const.mul (Complex.measurable_ofReal.comp measurable_sawtoothB1)).div ?_
    exact (measurable_const.add Complex.measurable_ofReal).pow_const 3
  have h_hasDeriv :
      HasDerivAt (fun z : ℂ ↦ ∫ t : ℝ in Ioi 0, F z t)
        (∫ t : ℝ in Ioi 0, F' s₀ t) s₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound) hV_nhds
      (Eventually.of_forall fun z ↦ (measurable_binetIntegrand z).aestronglyMeasurable)
      (integrableOn_Ioi_binetIntegrand hs₀)
      (hF'_meas s₀).aestronglyMeasurable ?_ ?_ ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht_pos : 0 < t := mem_Ioi.mp ht
      have hz_re : c < z.re := hz
      have hct_pos : 0 < c + t := by linarith
      have h_norm_ge : c + t ≤ ‖z + (t : ℂ)‖ := by
        have h1 : c + t ≤ z.re + t := by linarith
        exact h1.trans re_add_le_norm_add_ofReal
      have h_num : ‖-2 * (sawtoothB1 t : ℂ)‖ ≤ 1 := by
        rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        linarith [abs_sawtoothB1_le_half ht_pos.le]
      have h_den : c * (c + t) ^ 2 ≤ ‖z + (t : ℂ)‖ ^ 3 := by
        calc
          c * (c + t) ^ 2 ≤ (c + t) * (c + t) ^ 2 := by gcongr; linarith
          _ = (c + t) ^ 3 := by ring
          _ ≤ ‖z + (t : ℂ)‖ ^ 3 := pow_le_pow_left₀ hct_pos.le h_norm_ge 3
      dsimp [F', bound]
      rw [norm_div, norm_pow, one_div_mul_one_div]
      exact div_le_div₀ (by positivity) h_num (by positivity) h_den
    · exact (integrableOn_Ioi_one_div_add_sq hc).const_mul (1 / c)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht_pos : 0 < t := mem_Ioi.mp ht
      have hz_re : 0 < z.re := hc.trans hz
      have h_ne : z + (t : ℂ) ≠ 0 := add_ofReal_ne_zero hz_re ht_pos.le
      have hd_pow : HasDerivAt (fun w : ℂ ↦ (w + (t : ℂ)) ^ 2) (2 * (z + (t : ℂ))) z := by
        simpa [Pi.pow_def, pow_one] using ((hasDerivAt_id z).add_const (t : ℂ)).pow 2
      have hd_inv := (hd_pow.inv (pow_ne_zero 2 h_ne)).const_mul (sawtoothB1 t : ℂ)
      dsimp [F, F']
      rw [funext (fun w ↦ binetIntegrand_eq_sawtoothB1 w t)]
      simp only [div_eq_mul_inv]
      refine hd_inv.congr_deriv ?_
      field_simp [h_ne]
  exact h_hasDeriv.differentiableAt.differentiableWithinAt

/-- Complex differentiability of `Complex.digamma` on `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_digamma_rightHalfPlane :
    DifferentiableOn ℂ Complex.digamma {s : ℂ | 0 < s.re} := by
  have hU_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGamma : DifferentiableOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} := fun s hs ↦
    (Complex.differentiableAt_Gamma s (ne_neg_natCast_of_re_pos hs)).differentiableWithinAt
  have hGamma' : DifferentiableOn ℂ (deriv Complex.Gamma) {s : ℂ | 0 < s.re} :=
    hGamma.deriv hU_open
  rw [Complex.digamma_def]
  intro s hs
  exact ((hGamma' s hs).div (hGamma s hs) (Complex.Gamma_ne_zero_of_re_pos hs))

/-- **Euler–Maclaurin / Binet Integral Formula for `Complex.digamma s` (`0 < s.re`)**:
For all `s : ℂ` with `0 < s.re`,
$$\psi(s) = \log s - \frac{1}{2s}
  + \int_{t \in \operatorname{Ioi} 0} \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt.$$ -/
theorem digamma_eq_log_sub_half_inv_sub_integral {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s =
      Complex.log s - 1 / (2 * s) +
        ∫ t : ℝ in Ioi 0, (((t : ℂ) - ⌊t⌋₊ - 1 / 2) / (s + t) ^ 2) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_preconn : IsPreconnected U := convex_rightHalfPlane.isPreconnected
  have h1_mem : (1 : ℂ) ∈ U := by simp [U]
  have h_an1 : AnalyticOnNhd ℂ Complex.digamma U :=
    differentiableOn_digamma_rightHalfPlane.analyticOnNhd hU_open
  have h_diff_rhs :
      DifferentiableOn ℂ
        (fun z : ℂ ↦ Complex.log z - 1 / (2 * z) + ∫ t : ℝ in Ioi 0, binetIntegrand z t) U := by
    refine (DifferentiableOn.sub ?_ ?_).add differentiableOn_integral_binetIntegrand
    · refine fun z hz ↦ (Complex.differentiableAt_log ?_).differentiableWithinAt
      exact Complex.mem_slitPlane_iff.mpr (Or.inl hz)
    · refine fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_
      have hz_ne : 2 * z ≠ 0 := mul_ne_zero two_ne_zero (by
        intro h0; rw [h0] at hz; simp [U] at hz)
      exact (differentiableAt_const 1).div (differentiableAt_id.const_mul 2) hz_ne
  have h_an2 := h_diff_rhs.analyticOnNhd hU_open
  have h_tendsto : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt,
      eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht ↦ ofReal_ne_one.mpr ht)⟩
  have h_freq :
      ∃ᶠ z in 𝓝[≠] (1 : ℂ),
        Complex.digamma z =
          Complex.log z - 1 / (2 * z) + ∫ t : ℝ in Ioi 0, binetIntegrand z t := by
    refine h_tendsto.frequently ?_
    refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
    refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht ↦ ?_)
    exact digamma_ofReal_eq_eulerMaclaurin ht
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq h_an1 h_an2 hU_preconn h1_mem h_freq hs

/-!
## Section 3: Explicit Right-Half-Plane Bounds on `digamma` & Left-Vertical `logDeriv riemannZeta`
-/

/-- **First Binet Remainder Bound (`1 / (2 * s.re)`)**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{1}{2 \operatorname{Re} s}.$$ -/
theorem norm_digamma_sub_log_add_half_inv_le_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ 1 / (2 * s.re) := by
  have h_eq :
      Complex.digamma s - Complex.log s + 1 / (2 * s) =
        ∫ t : ℝ in Ioi 0, binetIntegrand s t := by
    have h := digamma_eq_log_sub_half_inv_sub_integral hs
    unfold binetIntegrand
    linear_combination h
  rw [h_eq]
  have h_bound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        ‖binetIntegrand s t‖ ≤ (1 / 2) * (1 / (s.re + t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (norm_binetIntegrand_le hs (mem_Ioi.mp ht).le).trans_eq (by ring)
  have h_int_le :=
    norm_integral_le_of_norm_le ((integrableOn_Ioi_one_div_add_sq hs).const_mul (1 / 2)) h_bound
  rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_add_sq hs,
    one_div_mul_one_div] at h_int_le
  exact h_int_le

/-- Corollary: for all `s : ℂ` with `0 < s.re`,
`‖Complex.digamma s - Complex.log s‖ ≤ 1 / (2 * ‖s‖) + 1 / (2 * s.re)`. -/
theorem norm_digamma_sub_log_le_norm_add_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 1 / (2 * ‖s‖) + 1 / (2 * s.re) := by
  have h_decomp :
      Complex.digamma s - Complex.log s =
        (-1 / (2 * s)) + (Complex.digamma s - Complex.log s + 1 / (2 * s)) := by ring
  rw [h_decomp]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_digamma_sub_log_add_half_inv_le_re hs))
  rw [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_ofNat]

/-- For `s : ℂ` with `0 ≤ s.re` and `t ≥ 0`, `‖s‖ ^ 2 + t ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2`. -/
theorem norm_sq_add_sq_le_norm_add_ofReal_sq {s : ℂ} (hs : 0 ≤ s.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖s‖ ^ 2 + t ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  have h_nonneg : 0 ≤ 2 * s.re * t := by positivity
  nlinarith

/-- Exact improper integral `∫ t in Ioi (0 : ℝ), 1 / (R ^ 2 + t ^ 2) = π / (2 * R)` for `R > 0`. -/
theorem integral_Ioi_one_div_sq_add_sq {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in Ioi 0, 1 / (R ^ 2 + t ^ 2)) = Real.pi / (2 * R) := by
  have hR_ne : R ≠ 0 := hR.ne'
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) (1 / (R ^ 2 + t ^ 2)) t := by
    intro t _
    have hpos : R ^ 2 + t ^ 2 ≠ 0 := by positivity
    have hd := (((hasDerivAt_id t).div_const R).arctan).const_mul (1 / R)
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp [hR_ne, hpos]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (R ^ 2 + t ^ 2) := fun t _ ↦ by positivity
  have htend :
      Tendsto (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) atTop (𝓝 (Real.pi / (2 * R))) := by
    have h_div : Tendsto (fun u : ℝ ↦ u / R) atTop atTop := tendsto_id.atTop_div_const hR
    have h_atan : Tendsto (fun u : ℝ ↦ Real.arctan (u / R)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h_div
    have h_mul := h_atan.const_mul (1 / R)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h_mul
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend]
  simp

/-- Integrability of `t ↦ 1 / (R ^ 2 + t ^ 2)` on `Ioi (0 : ℝ)` for `R > 0`. -/
theorem integrableOn_Ioi_one_div_sq_add_sq {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ ↦ 1 / (R ^ 2 + t ^ 2)) (Ioi 0) := by
  have hR_ne : R ≠ 0 := hR.ne'
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) (1 / (R ^ 2 + t ^ 2)) t := by
    intro t _
    have hpos : R ^ 2 + t ^ 2 ≠ 0 := by positivity
    have hd := (((hasDerivAt_id t).div_const R).arctan).const_mul (1 / R)
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp [hR_ne, hpos]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (R ^ 2 + t ^ 2) := fun t _ ↦ by positivity
  have htend :
      Tendsto (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) atTop (𝓝 (Real.pi / (2 * R))) := by
    have h_div : Tendsto (fun u : ℝ ↦ u / R) atTop atTop := tendsto_id.atTop_div_const hR
    have h_atan : Tendsto (fun u : ℝ ↦ Real.arctan (u / R)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h_div
    have h_mul := h_atan.const_mul (1 / R)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h_mul
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend

/-- **Sharp Right-Half-Plane Binet Remainder Bound (`π / (4 * ‖s‖)`)**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{\pi}{4 \|s\|}.$$ -/
theorem norm_digamma_sub_log_add_half_inv_le_norm {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ Real.pi / (4 * ‖s‖) := by
  have hs_norm : 0 < ‖s‖ := hs.trans_le (Complex.re_le_norm s)
  have h_eq :
      Complex.digamma s - Complex.log s + 1 / (2 * s) =
        ∫ t : ℝ in Ioi 0, binetIntegrand s t := by
    have h := digamma_eq_log_sub_half_inv_sub_integral hs
    unfold binetIntegrand
    linear_combination h
  rw [h_eq]
  have h_bound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        ‖binetIntegrand s t‖ ≤ (1 / 2) * (1 / (‖s‖ ^ 2 + t ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_nonneg : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [binetIntegrand_eq_sawtoothB1, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      ← div_eq_mul_one_div]
    exact div_le_div₀ (by norm_num) (abs_sawtoothB1_le_half ht_nonneg)
      (by positivity) (norm_sq_add_sq_le_norm_add_ofReal_sq hs.le ht_nonneg)
  have h_int_le :=
    norm_integral_le_of_norm_le ((integrableOn_Ioi_one_div_sq_add_sq hs_norm).const_mul (1 / 2))
      h_bound
  rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_sq_add_sq hs_norm] at h_int_le
  refine h_int_le.trans (le_of_eq ?_)
  ring

/-- **Uniform Right-Half-Plane Bound on `‖Complex.digamma s - Complex.log s‖`**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s\| \le \frac{2 + \pi}{4 \|s\|} \le \frac{2}{\|s\|}.$$ -/
theorem norm_digamma_sub_log_le_two_add_pi_div_four_norm {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ (2 + Real.pi) / (4 * ‖s‖) := by
  have h_decomp :
      Complex.digamma s - Complex.log s =
        (-1 / (2 * s)) + (Complex.digamma s - Complex.log s + 1 / (2 * s)) := by ring
  rw [h_decomp]
  have h1 : ‖-1 / (2 * s)‖ = 1 / (2 * ‖s‖) := by
    rw [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_ofNat]
  have h2 := norm_digamma_sub_log_add_half_inv_le_norm hs
  calc
    ‖(-1 / (2 * s)) + (Complex.digamma s - Complex.log s + 1 / (2 * s))‖
      ≤ ‖-1 / (2 * s)‖ + ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ := norm_add_le _ _
    _ ≤ 1 / (2 * ‖s‖) + Real.pi / (4 * ‖s‖) := by linarith
    _ = (2 + Real.pi) / (4 * ‖s‖) := by ring

/-- For any `z : ℂ` with `1 < z.re`, `‖logDeriv riemannZeta z‖ ≤ ‖logDeriv riemannZeta (z.re : ℂ)‖`
via the absolute convergence of the von Mangoldt L-series `L ↗Λ`. -/
theorem norm_logDeriv_riemannZeta_le_of_one_lt_re {z : ℂ} (hz : 1 < z.re) :
    ‖logDeriv riemannZeta z‖ ≤ ‖logDeriv riemannZeta (z.re : ℂ)‖ := by
  have hz_re : 1 < (z.re : ℂ).re := by simpa using hz
  have h1 : logDeriv riemannZeta z = -L ↗Λ z := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz, logDeriv_apply,
      neg_div, neg_neg]
  have h2 : logDeriv riemannZeta (z.re : ℂ) = -L ↗Λ (z.re : ℂ) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz_re, logDeriv_apply,
      neg_div, neg_neg]
  rw [h1, h2, norm_neg, norm_neg]
  have h_sum : Summable fun n : ℕ ↦ ‖LSeries.term ↗Λ z n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hz).norm
  have h_term : ∀ n : ℕ, LSeries.term ↗Λ (z.re : ℂ) n = ((‖LSeries.term ↗Λ z n‖ : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.norm_term_eq]
      simp only [hn, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_div,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have h_tsum_re : L ↗Λ (z.re : ℂ) = ((∑' n : ℕ, ‖LSeries.term ↗Λ z n‖ : ℝ) : ℂ) := by
    unfold LSeries
    rw [tsum_congr h_term, Complex.ofReal_tsum]
  rw [h_tsum_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)]
  exact norm_tsum_le_tsum_norm h_sum

/-- Exact identity for
`Complex.normSq (Complex.cos (x + y * I)) - Complex.normSq (Complex.sin (x + y * I))`:
for all `x, y : ℝ`,
$$\operatorname{normSq}(\cos(x + y i)) - \operatorname{normSq}(\sin(x + y i)) = \cos(2x).$$ -/
theorem normSq_cos_sub_normSq_sin (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) -
      Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) = Real.cos (2 * x) := by
  rw [Complex.cos_add_mul_I, Complex.sin_add_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, zero_mul,
    add_zero, I_im, mul_one, sub_self, sub_im, mul_im, add_im]
  calc
    _ = (Real.cos x ^ 2 - Real.sin x ^ 2) * (Real.cosh y ^ 2 - Real.sinh y ^ 2) := by ring
    _ = Real.cos (2 * x) := by rw [Real.cosh_sq_sub_sinh_sq y, mul_one, ← Real.cos_two_mul']

/-- For all `t : ℝ`, `Complex.cos (π * (-1 / 4 + (t : ℂ) * I) / 2) ≠ 0` and
`‖Complex.tan (π * (-1 / 4 + (t : ℂ) * I) / 2)‖ ≤ 1`. -/
theorem cos_ne_zero_and_norm_tan_le_one_leftVertical (t : ℝ) :
    Complex.cos (π * ((-1 / 4 : ℂ) + (t : ℂ) * I) / 2) ≠ 0 ∧
      ‖Complex.tan (π * ((-1 / 4 : ℂ) + (t : ℂ) * I) / 2)‖ ≤ 1 := by
  set x : ℝ := -Real.pi / 8
  set y : ℝ := Real.pi * t / 2
  have h_arg : π * ((-1 / 4 : ℂ) + (t : ℂ) * I) / 2 = (x : ℂ) + (y : ℂ) * I := by
    dsimp [x, y]
    push_cast
    ring
  rw [h_arg]
  have h_diff := normSq_cos_sub_normSq_sin x y
  have h_cos2x : Real.cos (2 * x) = Real.sqrt 2 / 2 := by
    have h2x : 2 * x = -(Real.pi / 4) := by dsimp [x]; ring
    rw [h2x, Real.cos_neg, Real.cos_pi_div_four]
  rw [h_cos2x] at h_diff
  have h_sqrt2_pos : 0 < Real.sqrt 2 / 2 := by positivity
  have h_sin_nonneg : 0 ≤ Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) :=
    Complex.normSq_nonneg _
  have h_cos_pos : 0 < Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) := by linarith
  have h_cos_ne : Complex.cos ((x : ℂ) + (y : ℂ) * I) ≠ 0 :=
    Complex.normSq_pos.mp h_cos_pos
  refine ⟨h_cos_ne, ?_⟩
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  have h_norm_cos_pos : 0 < ‖Complex.cos ((x : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr h_cos_ne
  rw [div_le_one₀ h_norm_cos_pos]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  linarith

/-- For all `t : ℝ`, `(-1 / 4 : ℂ) + (t : ℂ) * I` is not an integer `(n : ℂ)`. -/
theorem leftVertical_ne_intCast (t : ℝ) (n : ℤ) :
    (-1 / 4 : ℂ) + (t : ℂ) * I ≠ (n : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [add_re, neg_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_self, add_zero, intCast_re] at hre
  have h4_real : (-1 : ℝ) = ((4 * n : ℤ) : ℝ) := by push_cast; linarith
  have h4 : (-1 : ℤ) = 4 * n := by exact_mod_cast h4_real
  omega

end ConjectureMachines.Semantics.Riemann.DigammaBinet
