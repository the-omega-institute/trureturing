/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Fourier line Laplace transforms of the inclusive Mangoldt ramp and U. -/
/- Complete arithmetic source candidate; final admission pending.
   All arithmetic sums below use the complete actual
   von Mangoldt function, and U is the existing CompleteMertensPeak.U. -/
import D5.S3.Weil.Mertens.IntegratedExplicit.TrivialZeroLaplace
import D5.S3.Arith.Robin.CompleteMertensPeak
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit

open D5.S3.Arith.Robin.CompleteMertensPeak

/-- Locally finite positive-part representation; n=0 and n=1 vanish. -/
def mangoldtRamp (n : ℕ) (t : ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * max (t / (n : ℝ) - 1) 0

def mangoldtPart (t : ℝ) : ℝ := ∑' n : ℕ, mangoldtRamp n t

theorem mangoldtRamp_nonneg (n : ℕ) (t : ℝ) : 0 ≤ mangoldtRamp n t :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

theorem mangoldtRamp_continuous (n : ℕ) : Continuous (mangoldtRamp n) := by
  change Continuous (fun t : ℝ =>
    ArithmeticFunction.vonMangoldt n * max (t / (n : ℝ) - 1) 0)
  fun_prop

/-- In particular, a prime-power term has value zero when it enters the
inclusive floor sum. No exception for integer or prime-power endpoints. -/
theorem mangoldtRamp_at_entry (n : ℕ) : mangoldtRamp n (n : ℝ) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtRamp]
  · simp [mangoldtRamp, Nat.cast_ne_zero.mpr hn]

private theorem ramp_zero_of_lt {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (h : t < n) :
    mangoldtRamp n t = 0 := by
  have hn : (0 : ℝ) < n := lt_of_le_of_lt ht h
  dsimp only [mangoldtRamp]
  rw [max_eq_right (by
    have := (div_lt_one hn).mpr h
    linarith)]
  exact mul_zero _

private theorem ramp_eq_affine {n : ℕ} {t : ℝ}
    (hn : 0 < n) (h : (n : ℝ) ≤ t) :
    mangoldtRamp n t = ArithmeticFunction.vonMangoldt n * (t / (n : ℝ) - 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only [mangoldtRamp]
  rw [max_eq_left (by have := (one_le_div hn').mpr h; linarith)]

private theorem ramp_support {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 ⌊t⌋₊) : mangoldtRamp n t = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [mangoldtRamp]
  · have hnf : ⌊t⌋₊ < n := by
      simp only [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hn
      omega
    exact ramp_zero_of_lt ht (Nat.lt_of_floor_lt hnf)

theorem mangoldtPart_summable {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n : ℕ => mangoldtRamp n t) :=
  summable_of_ne_finset_zero (ramp_support ht)

/-- Exact complete finite U, with the same inclusive floor endpoint as its owner. -/
theorem U_eq_complete_ramps {t : ℝ} (ht : 0 ≤ t) :
    U t = mangoldtPart t - t * Real.log t +
      (1 + Real.eulerMascheroniConstant) * t := by
  have hp : mangoldtPart t =
      ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊,
        ArithmeticFunction.vonMangoldt n * (t / (n : ℝ) - 1) := by
    rw [mangoldtPart, tsum_eq_sum (s := Finset.Ioc 0 ⌊t⌋₊) (ramp_support ht)]
    apply Finset.sum_congr rfl
    intro n hn
    exact ramp_eq_affine (Finset.mem_Ioc.mp hn).1
      ((Nat.le_floor_iff ht).mp (Finset.mem_Ioc.mp hn).2)
  rw [hp, U, Chebyshev.psi]
  have hs : (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊,
      ArithmeticFunction.vonMangoldt n * (t / (n : ℝ) - 1)) =
      t * (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hs]

private theorem mangoldtPart_eq_range {t : ℝ} (ht : 0 ≤ t) {N : ℕ}
    (hN : t < N) : mangoldtPart t = ∑ n ∈ Finset.range N, mangoldtRamp n t := by
  apply tsum_eq_sum
  intro n hn
  have hnN : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  exact ramp_zero_of_lt ht (hN.trans_le (by exact_mod_cast hnN))

/-- The locally finite representation gives actual continuity of the old U,
including every prime-power endpoint; floor itself is never differentiated. -/
theorem U_continuousAt_pos {t : ℝ} (ht : 0 < t) : ContinuousAt U t := by
  let N : ℕ := ⌈t + 1⌉₊ + 1
  have htN : t < (N : ℝ) := by
    have hc := Nat.le_ceil (t + 1)
    dsimp only [N]
    push_cast
    linarith
  have he : U =ᶠ[𝓝 t] (fun u : ℝ =>
      (∑ n ∈ Finset.range N, mangoldtRamp n u) - u * Real.log u +
        (1 + Real.eulerMascheroniConstant) * u) := by
    filter_upwards [Ioo_mem_nhds ht htN] with u hu
    rw [U_eq_complete_ramps hu.1.le, mangoldtPart_eq_range hu.1.le hu.2]
  have hc : ContinuousAt (fun u : ℝ =>
      (∑ n ∈ Finset.range N, mangoldtRamp n u) - u * Real.log u +
        (1 + Real.eulerMascheroniConstant) * u) t := by
    apply ContinuousAt.add
    · apply ContinuousAt.sub
      · exact (continuous_finsetSum _ (fun n _ => mangoldtRamp_continuous n)).continuousAt
      · exact continuousAt_id.mul (Real.continuousAt_log ht.ne')
    · fun_prop
  exact hc.congr_of_eventuallyEq he

theorem U_exp_continuous : Continuous (fun y : ℝ => U (Real.exp y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact (U_continuousAt_pos (Real.exp_pos y)).comp Real.continuous_exp.continuousAt

/-- Complete arithmetic endpoint statement for the final finite endpoint application. -/
theorem complete_mangoldt_endpoint (n : ℕ) (hn : 0 < n) :
    mangoldtRamp n n = 0 ∧ ContinuousAt U (n : ℝ) ∧
      U n = (∑ k ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt k * ((n : ℝ) / (k : ℝ) - 1)) -
          (n : ℝ) * Real.log n + (1 + Real.eulerMascheroniConstant) * n := by
  refine ⟨mangoldtRamp_at_entry n, U_continuousAt_pos (by exact_mod_cast hn), ?_⟩
  rw [U_eq_complete_ramps (Nat.cast_nonneg n), mangoldtPart,
    tsum_eq_sum (s := Finset.Ioc 0 n) (by
      simpa only [Nat.floor_natCast] using ramp_support (Nat.cast_nonneg n))]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  exact ramp_eq_affine (Finset.mem_Ioc.mp hk).1 (by
    exact_mod_cast (Finset.mem_Ioc.mp hk).2)

/-- Line Re(s)=2, in Mathlib's Fourier normalization. -/
def transformLine (t : ℝ) : ℂ := 2 + (2 * Real.pi * t : ℝ) * Complex.I

@[simp] theorem transformLine_re (t : ℝ) : (transformLine t).re = 2 := by
  simp [transformLine]

private theorem ramp_laplace_function {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (Ioi (0 : ℝ)).indicator (fun y : ℝ =>
      Complex.exp (-s * y) * (mangoldtRamp n (Real.exp y) : ℂ)) =
    (Ioi (Real.log n)).indicator (fun y : ℝ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Complex.exp ((1 - s) * y) / (n : ℂ) - Complex.exp (-s * y))) := by
  funext y
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  by_cases hy : Real.log n < y
  · have hy0 : y ∈ Ioi (0 : ℝ) := lt_of_le_of_lt hlog hy
    have hne : (n : ℝ) < Real.exp y := (Real.log_lt_iff_lt_exp hn0).mp hy
    rw [Set.indicator_of_mem hy0,
      Set.indicator_of_mem (show y ∈ Ioi (Real.log n) from hy),
      ramp_eq_affine (Nat.pos_of_ne_zero hn) hne.le]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_exp]
    have he : Complex.exp ((1 - s) * y) =
        Complex.exp (-s * y) * Complex.exp (y : ℂ) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    ring
  · rw [Set.indicator_of_notMem (show y ∉ Ioi (Real.log n) from hy)]
    by_cases hy0 : y ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hy0]
      have hne : Real.exp y ≤ (n : ℝ) := (Real.le_log_iff_exp_le hn0).mp (le_of_not_gt hy)
      have hr : mangoldtRamp n (Real.exp y) = 0 := by
        dsimp only [mangoldtRamp]
        rw [max_eq_right (by have := (div_le_one hn0).mpr hne; linarith), mul_zero]
      simp only [hr, Complex.ofReal_zero, mul_zero]
    · rw [Set.indicator_of_notMem hy0]

/-- The integral of each complete ramp is explicit before any exchange. -/
theorem mangoldtRamp_laplace {n : ℕ} {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) *
      (mangoldtRamp n (Real.exp y) : ℂ)) =
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n /
        (s * (s - 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtRamp]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hns : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    exact Complex.exp_ne_zero _
  have hs0 : s ≠ 0 := by intro e; rw [e] at hs; norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro e
    have := congrArg Complex.re e
    simp at this
    linarith
  rw [← integral_indicator measurableSet_Ioi, ramp_laplace_function hn s,
    integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_sub ((integrableOn_exp_mul_complex_Ioi (by
      simp only [Complex.sub_re, Complex.one_re]; linarith) (Real.log n)).div_const _)
      (integrableOn_exp_mul_complex_Ioi (by simp; linarith) (Real.log n)),
    integral_div, integral_exp_mul_complex_Ioi (by simp; linarith),
    integral_exp_mul_complex_Ioi (by simp; linarith), LSeries.term_of_ne_zero hn]
  have hpow : Complex.exp (-s * (Real.log n : ℂ)) = (n : ℂ) ^ (-s) := by
    have hlogC : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hn0.le).symm
    rw [Complex.cpow_def_of_ne_zero hnC, hlogC]
    congr 1
    ring
  have hshift : Complex.exp ((1 - s) * (Real.log n : ℂ)) =
      (n : ℂ) * Complex.exp (-s * (Real.log n : ℂ)) := by
    rw [show (1 - s) * (Real.log n : ℂ) =
      (Real.log n : ℂ) + -s * (Real.log n : ℂ) by ring, Complex.exp_add,
      ← Complex.ofReal_exp, Real.exp_log hn0]
    simp only [Complex.ofReal_natCast]
  rw [hshift]
  simp_rw [hpow, Complex.cpow_neg]
  rw [show 1 - s = -(s - 1) by ring]
  field_simp [hnC, hs0, hs1, hns]
  <;> ring

theorem mangoldtRamp_laplace_integrable {n : ℕ} {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      (mangoldtRamp n (Real.exp y) : ℂ)) (Ioi 0) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtRamp]
  rw [← integrable_indicator_iff measurableSet_Ioi, ramp_laplace_function hn s,
    integrable_indicator_iff measurableSet_Ioi]
  exact (((integrableOn_exp_mul_complex_Ioi (by simp; linarith) _).div_const _).sub
    (integrableOn_exp_mul_complex_Ioi (by simp; linarith) _)).const_mul _

/-- Absolute integral of every ramp on the entire Fourier line. -/
theorem mangoldtRamp_laplace_norm (t : ℝ) (n : ℕ) :
    (∫ y : ℝ in Ioi 0, ‖Complex.exp (-transformLine t * y) *
      (mangoldtRamp n (Real.exp y) : ℂ)‖) =
        ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ 2) / 2 := by
  have he (y : ℝ) : ‖Complex.exp (-transformLine t * y) *
      (mangoldtRamp n (Real.exp y) : ℂ)‖ =
      (Complex.exp (-(2 : ℂ) * y) * (mangoldtRamp n (Real.exp y) : ℂ)).re := by
    have he : Complex.exp (-(2 : ℂ) * (y : ℂ)) = (Real.exp (-2 * y) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    calc
      _ = Real.exp (-2 * y) * mangoldtRamp n (Real.exp y) := by
        simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mangoldtRamp_nonneg n _)]
        congr 2
        simp [Complex.mul_re, Complex.neg_re]
      _ = _ := by
        rw [he]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp_rw [he]
  change (∫ y : ℝ in Ioi 0,
    RCLike.re (Complex.exp (-(2 : ℂ) * y) * (mangoldtRamp n (Real.exp y) : ℂ))) = _
  rw [integral_re (mangoldtRamp_laplace_integrable (n := n)
      (by norm_num : 1 < (2 : ℂ).re)),
    mangoldtRamp_laplace (by norm_num : 1 < (2 : ℂ).re),
    LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0)]
  have hr : (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (2 : ℕ) /
      ((2 : ℂ) * (2 - 1)) =
      ((ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [Complex.cpow_ofNat, hr]
  rfl

theorem mangoldtRamp_norm_integrals_summable (t : ℝ) :
    Summable (fun n : ℕ => ∫ y : ℝ in Ioi 0,
      ‖Complex.exp (-transformLine t * y) * (mangoldtRamp n (Real.exp y) : ℂ)‖) := by
  have hs := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (by norm_num : 1 < (2 : ℂ).re)).norm
  have he (n : ℕ) :
      ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
    rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0)]
    simp [norm_div, Complex.cpow_ofNat, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  simpa only [mangoldtRamp_laplace_norm, he] using hs.div_const 2

private theorem weighted_ramps_hasSum (t y : ℝ) :
    HasSum (fun n : ℕ => Complex.exp (-transformLine t * y) *
      (mangoldtRamp n (Real.exp y) : ℂ))
      (Complex.exp (-transformLine t * y) * (mangoldtPart (Real.exp y) : ℂ)) := by
  exact (Complex.hasSum_ofReal.mpr
    (mangoldtPart_summable (Real.exp_nonneg y)).hasSum).mul_left _

/-- Tonelli is paid at the norm level, before the complex integral is exchanged.
The positive ENNReal sum is finite by the actual Mangoldt LSeries at 2. -/
theorem mangoldtPart_line_integrable (t : ℝ) :
    IntegrableOn (fun y : ℝ => Complex.exp (-transformLine t * y) *
      (mangoldtPart (Real.exp y) : ℂ)) (Ioi 0) := by
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-transformLine t * y) *
    (mangoldtRamp n (Real.exp y) : ℂ)
  let g : ℝ → ℂ := fun y => Complex.exp (-transformLine t * y) *
    (mangoldtPart (Real.exp y) : ℂ)
  have hi : ∀ n, Integrable (f n) (volume.restrict (Ioi 0)) := fun n =>
    mangoldtRamp_laplace_integrable (by simp : 1 < (transformLine t).re)
  have hm : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
    have hp : Continuous (fun y : ℝ => mangoldtPart (Real.exp y)) := by
      have he : (fun y : ℝ => mangoldtPart (Real.exp y)) =
          (fun y : ℝ => U (Real.exp y) + Real.exp y * y -
            (1 + Real.eulerMascheroniConstant) * Real.exp y) := by
        funext y
        have h := U_eq_complete_ramps (Real.exp_nonneg y)
        rw [Real.log_exp] at h
        linarith only [h]
      rw [he]
      exact (U_exp_continuous.add (by fun_prop)).sub (by fun_prop)
    exact (show Continuous g by dsimp only [g]; fun_prop).aestronglyMeasurable
  refine ⟨hm, (hasFiniteIntegral_iff_norm g).mpr ?_⟩
  calc
    (∫⁻ y : ℝ, ENNReal.ofReal ‖g y‖ ∂volume.restrict (Ioi 0)) ≤
        ∫⁻ y : ℝ, ∑' n : ℕ, ENNReal.ofReal ‖f n y‖ ∂volume.restrict (Ioi 0) := by
      apply lintegral_mono
      intro y
      have hh : HasSum (fun n => f n y) (g y) := weighted_ramps_hasSum t y
      change ENNReal.ofReal ‖g y‖ ≤ ∑' n : ℕ, ENNReal.ofReal ‖f n y‖
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg (f n y)) hh.summable.norm]
      exact ENNReal.ofReal_le_ofReal (by
        rw [← hh.tsum_eq]
        exact norm_tsum_le_tsum_norm hh.summable.norm)
    _ = ∑' n : ℕ, ENNReal.ofReal
        (∫ y : ℝ in Ioi 0, ‖f n y‖) := by
      rw [lintegral_tsum (fun n => (hi n).aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal)]
      congr 1
      funext n
      simpa only [ofReal_norm] using
        (ofReal_integral_norm_eq_lintegral_enorm (hi n)).symm
    _ < ⊤ := (mangoldtRamp_norm_integrals_summable t).tsum_ofReal_lt_top

/-- Absolute summation, now exchanged with the complex Laplace integral. -/
theorem mangoldtPart_line_laplace (t : ℝ) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) *
      (mangoldtPart (Real.exp y) : ℂ)) =
        (-deriv riemannZeta (transformLine t) / riemannZeta (transformLine t)) /
          (transformLine t * (transformLine t - 1)) := by
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-transformLine t * y) *
    (mangoldtRamp n (Real.exp y) : ℂ)
  have hi : ∀ n, Integrable (f n) (volume.restrict (Ioi 0)) := fun n =>
    mangoldtRamp_laplace_integrable (by simp : 1 < (transformLine t).re)
  have hx := hasSum_integral_of_summable_integral_norm hi
    (mangoldtRamp_norm_integrals_summable t)
  have hx' : HasSum
      (fun n : ℕ => LSeries.term
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (transformLine t) n /
          (transformLine t * (transformLine t - 1)))
      (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) *
        (mangoldtPart (Real.exp y) : ℂ)) := by
    convert hx using 1
    · funext n
      exact (mangoldtRamp_laplace (by simp : 1 < (transformLine t).re)).symm
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      exact (weighted_ramps_hasSum t y).tsum_eq.symm
  have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (by simp : 1 < (transformLine t).re)).hasSum.div_const
      (transformLine t * (transformLine t - 1))
  change HasSum _ (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
    (transformLine t) / (transformLine t * (transformLine t - 1))) at hL
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (by simp : 1 < (transformLine t).re)] at hL
  exact hx'.unique hL

private theorem first_exp_moment_integrable (t : ℝ) :
    IntegrableOn (fun y : ℝ => (y : ℂ) *
      Complex.exp ((1 - transformLine t) * y)) (Ioi 0) := by
  have hr : IntegrableOn (fun y : ℝ => y * Real.exp (-y)) (Ioi 0) := by
    simpa only [Real.rpow_one, one_mul, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 : ℝ)) (p := (1 : ℝ)) (b := (1 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  refine hr.mono' (by
    exact (show Continuous (fun y : ℝ => (y : ℂ) *
      Complex.exp ((1 - transformLine t) * y)) by fun_prop).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact le_of_eq (by
    norm_num [norm_mul, Complex.norm_exp, abs_of_nonneg (show 0 < y from hy).le])

/-- The first exponential moment on the whole line, with the boundary at infinity paid. -/
theorem first_exp_moment (t : ℝ) :
    (∫ y : ℝ in Ioi 0, (y : ℂ) * Complex.exp ((1 - transformLine t) * y)) =
      1 / (transformLine t - 1) ^ 2 := by
  let a : ℂ := 1 - transformLine t
  have ha : a.re = -1 := by norm_num [a]
  have ha0 : a ≠ 0 := by intro e; simp [e] at ha
  let p : ℝ → ℂ := fun y => Complex.exp (a * y) * ((y : ℂ) / a - 1 / a ^ 2)
  have hd (y : ℝ) : HasDerivAt p ((y : ℂ) * Complex.exp (a * y)) y := by
    have he := ((hasDerivAt_id y).ofReal_comp.const_mul a).cexp
    have hl := ((hasDerivAt_id y).ofReal_comp.div_const a).sub_const (1 / a ^ 2)
    convert he.mul hl using 1
    · rfl
    · simp only [id_eq, Complex.ofReal_one]
      field_simp [ha0]
      <;> ring
  have hlim : Tendsto p atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb : ∀ᶠ y : ℝ in atTop, ‖p y‖ ≤
        (y * Real.exp (-y)) / ‖a‖ + Real.exp (-y) / ‖a‖ ^ 2 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
      calc
        ‖p y‖ ≤ Real.exp (-y) * (‖(y : ℂ) / a‖ + ‖1 / a ^ 2‖) := by
          dsimp only [p]
          rw [norm_mul, Complex.norm_exp]
          have har : (a * (y : ℂ)).re = -y := by simp [Complex.mul_re, ha]
          rw [har]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_nonneg _)
        _ = _ := by simp [norm_div, norm_pow, abs_of_nonneg hy]; ring
    have hl : Tendsto (fun y : ℝ =>
        (y * Real.exp (-y)) / ‖a‖ + Real.exp (-y) / ‖a‖ ^ 2) atTop (𝓝 0) := by
      simpa only [pow_one, pow_zero, one_mul, zero_div, add_zero] using
        ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).div_const ‖a‖).add
          ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).div_const (‖a‖ ^ 2))
    exact squeeze_zero' (Eventually.of_forall (fun y => norm_nonneg (p y))) hb hl
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y _ => hd y) (first_exp_moment_integrable t) hlim
  simpa only [p, Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_div, zero_sub, one_mul,
    neg_neg, a, show 1 - transformLine t = -(transformLine t - 1) by ring,
    neg_sq] using h

private theorem U_weighted_split (s : ℂ) (y : ℝ) :
    Complex.exp (-s * y) * (U (Real.exp y) : ℂ) =
      Complex.exp (-s * y) * (mangoldtPart (Real.exp y) : ℂ) -
        (y : ℂ) * Complex.exp ((1 - s) * y) +
          ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) * Complex.exp ((1 - s) * y) := by
  rw [U_eq_complete_ramps (Real.exp_nonneg y), Real.log_exp]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_exp]
  have he : Complex.exp (-s * y) * Complex.exp (y : ℂ) =
      Complex.exp ((1 - s) * y) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = Complex.exp (-s * y) * (mangoldtPart (Real.exp y) : ℂ) -
        (y : ℂ) * (Complex.exp (-s * y) * Complex.exp (y : ℂ)) +
          ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
            (Complex.exp (-s * y) * Complex.exp (y : ℂ)) := by push_cast; ring
    _ = _ := by rw [he]; push_cast; rfl

theorem U_line_integrable (t : ℝ) :
    IntegrableOn (fun y : ℝ => Complex.exp (-transformLine t * y) *
      (U (Real.exp y) : ℂ)) (Ioi 0) := by
  have hi := (mangoldtPart_line_integrable t).sub (first_exp_moment_integrable t)
  have he := (integrableOn_exp_mul_complex_Ioi
    (by simp : (1 - transformLine t).re < 0) 0).const_mul
      ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
  exact (hi.add he).congr (Eventually.of_forall fun y => (U_weighted_split _ y).symm)

/-- The exact arithmetic Laplace transform. No error-tail or PNT hypothesis. -/
theorem U_line_laplace (t : ℝ) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) *
      (U (Real.exp y) : ℂ)) =
      (-deriv riemannZeta (transformLine t) / riemannZeta (transformLine t)) /
        (transformLine t * (transformLine t - 1)) -
          1 / (transformLine t - 1) ^ 2 +
            ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (transformLine t - 1) := by
  simp_rw [U_weighted_split]
  have hconst : IntegrableOn (fun y : ℝ =>
      ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        Complex.exp ((1 - transformLine t) * y)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi
      (by simp : (1 - transformLine t).re < 0) 0).const_mul _
  rw [integral_add (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun y : ℝ =>
      Complex.exp (-transformLine t * y) * (mangoldtPart (Real.exp y) : ℂ) -
        (y : ℂ) * Complex.exp ((1 - transformLine t) * y))
    (g := fun y : ℝ => ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
      Complex.exp ((1 - transformLine t) * y))
    ((mangoldtPart_line_integrable t).sub (first_exp_moment_integrable t))
    hconst,
    integral_sub (f := fun y : ℝ => Complex.exp (-transformLine t * y) *
      (mangoldtPart (Real.exp y) : ℂ))
      (g := fun y : ℝ => (y : ℂ) * Complex.exp ((1 - transformLine t) * y))
      (mangoldtPart_line_integrable t) (first_exp_moment_integrable t),
    mangoldtPart_line_laplace, first_exp_moment, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simp : (1 - transformLine t).re < 0)]
  rw [show 1 - transformLine t = -(transformLine t - 1) by ring]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_neg]
  ring

end D5.S3.Weil.Mertens.IntegratedExplicit
end

