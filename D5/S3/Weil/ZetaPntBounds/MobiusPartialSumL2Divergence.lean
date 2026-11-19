/- GID: D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unconditional divergence of the literal weighted Möbius partial sum in half-line L². -/

/-
The arithmetic front end is retained from the accepted literal source.
The half-line L² pairing and local analytic-derivative argument follows the
substantive proof pattern in D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.lean.
That module records the related jrgochan/prime HilbertSetup attribution; this
module uses only the checked declarations imported below.
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Basic.Complex.BigOperators
import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

/-! Unconditional literal weighted Möbius partial-sum divergence and its half-line Mellin L² bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Asymptotics
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open scoped BigOperators Topology ArithmeticFunction.Moebius
open scoped ENNReal InnerProductSpace

namespace D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence

/-! ## The literal source function and the exact target -/

abbrev halfLineMeasure : Measure ℝ := volume.restrict (Ioi (1 : ℝ))

/-- The actual finite weighted Möbius partial sum.  The `Icc` cutoff is the
literal integer interval `1 ≤ n ≤ floor x`; no abstract transform is used. -/
def mobiusPartialSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)

/-! ## The discrete Möbius Dirichlet-series side -/

private def mobiusComplex (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)

private def weightedMobius (n : ℕ) : ℂ := mobiusComplex n / (n : ℂ)

private def weightedPartialSum (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, weightedMobius n

private theorem weightedPartialSum_eq_ofReal (x : ℝ) :
    weightedPartialSum x = (mobiusPartialSum x : ℂ) := by
  simp only [weightedPartialSum, mobiusPartialSum, weightedMobius, mobiusComplex,
    Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]

/-!
The next identity is the exact shift needed for the initial Mellin formula:

  L(μ(n)/n,s) = L(μ,s+1).

It uses only `Complex.cpow_add` at a positive integer base.  The L-series
itself is the pinned Mathlib definition, so the zero term is handled
explicitly rather than by a convention about `0⁰`.
-/
private theorem weightedTerm_shift (s : ℂ) (n : ℕ) :
    LSeries.term weightedMobius s n = LSeries.term mobiusComplex (s + 1) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [weightedMobius, div_div, Complex.cpow_add s 1 (Nat.cast_ne_zero.mpr hn),
      Complex.cpow_one, mul_comm (n : ℂ) ((n : ℂ) ^ s)]

private theorem weightedLSeries_shift (s : ℂ) :
    LSeries weightedMobius s = LSeries mobiusComplex (s + 1) := by
  rw [LSeries]
  apply tsum_congr
  exact weightedTerm_shift s

private theorem weightedLSeries_summable {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable weightedMobius s := by
  change Summable (LSeries.term weightedMobius s)
  apply (summable_congr (weightedTerm_shift s)).2
  change Summable (LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (s + 1))
  exact (ArithmeticFunction.LSeriesSummable_moebius_iff (s := s + 1)).mpr
    (by simpa using hs)

/-! The partial sums have logarithmic absolute growth. -/
private def WeightedMobiusGrowth : Prop :=
  ∀ {r : ℝ}, 0 < r →
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, weightedMobius k) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ r)

private theorem weightedMobius_norm_le_inv {n : ℕ} (hn : 1 ≤ n) :
    ‖weightedMobius n‖ ≤ (n : ℝ)⁻¹ := by
  rw [weightedMobius, norm_div]
  have hμ : ‖mobiusComplex n‖ ≤ 1 := by
    rw [mobiusComplex, Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hden : ‖(n : ℂ)‖ = (n : ℝ) := by
    simp
  rw [hden]
  simpa only [one_div] using
    div_le_div_of_nonneg_right hμ (show (0 : ℝ) ≤ n by positivity)

private theorem weightedPartialSum_norm_le_harmonic (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, weightedMobius k‖ ≤ (harmonic n : ℝ) := by
  calc
    ‖∑ k ∈ Finset.Icc 1 n, weightedMobius k‖ ≤
        ∑ k ∈ Finset.Icc 1 n, ‖weightedMobius k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      exact weightedMobius_norm_le_inv (Finset.mem_Icc.mp hk).1
    _ = (harmonic n : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem weightedMobiusGrowth_proved : WeightedMobiusGrowth := by
  intro r hr
  refine isBigO_iff.mpr ⟨1 + r⁻¹, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum := weightedPartialSum_norm_le_harmonic n
  have hH := harmonic_le_one_add_log n
  have hlog := Real.log_natCast_le_rpow_div n hr
  have hnpow : 1 ≤ (n : ℝ) ^ r := by
    exact Real.one_le_rpow hnR hr.le
  have hrinv : 0 ≤ r⁻¹ := by positivity
  have hbound :
      ‖∑ k ∈ Finset.Icc 1 n, weightedMobius k‖ ≤
        (1 + r⁻¹) * (n : ℝ) ^ r := by
    calc
      _ ≤ (harmonic n : ℝ) := hsum
      _ ≤ 1 + Real.log (n : ℝ) := hH
      _ ≤ 1 + (n : ℝ) ^ r / r := by linarith
      _ ≤ (1 + r⁻¹) * (n : ℝ) ^ r := by
        rw [div_eq_mul_inv]
        nlinarith
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (le_trans (by norm_num) hnR) r)] using hbound

private def mobiusMellin (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (mobiusPartialSum x : ℂ) *
    (x : ℂ) ^ (-(s + 1))

/-!
This is the actual initial Mellin identity.  The parameterized form exposes
the reusable growth input, and the following specialization discharges it
from the displayed finite sum.
-/
private theorem initial_mellin_identity_of_growth
    (hg : WeightedMobiusGrowth) {s : ℂ} (hs : 0 < s.re) :
    s * mobiusMellin s = 1 / riemannZeta (s + 1) := by
  let r : ℝ := s.re / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrs : r < s.re := by
    dsimp [r]
    linarith
  have hO := hg hr
  have hrep := LSeries_eq_mul_integral weightedMobius hr.le hrs
    (weightedLSeries_summable hs) hO
  have hinter :
      (∫ t in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, weightedMobius k) *
          (t : ℂ) ^ (-(s + 1))) = mobiusMellin s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change weightedPartialSum t * (t : ℂ) ^ (-(s + 1)) =
      (mobiusPartialSum t : ℂ) * (t : ℂ) ^ (-(s + 1))
    rw [weightedPartialSum_eq_ofReal]
  have hL : LSeries weightedMobius s = s * mobiusMellin s := by
    calc
      LSeries weightedMobius s = s *
          (∫ t in Ioi (1 : ℝ),
            (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, weightedMobius k) *
              (t : ℂ) ^ (-(s + 1))) := hrep
      _ = s * mobiusMellin s := by rw [hinter]
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius
    (s := s + 1) (by simpa using hs)
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by simpa using hs)] at hprod
  have hprod' : riemannZeta (s + 1) * LSeries weightedMobius s = 1 := by
    rw [weightedLSeries_shift]
    exact hprod
  have hz : riemannZeta (s + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  apply (eq_div_iff hz).2
  calc
    (s * mobiusMellin s) * riemannZeta (s + 1) =
        riemannZeta (s + 1) * (s * mobiusMellin s) := mul_comm _ _
    _ =
        riemannZeta (s + 1) * LSeries weightedMobius s := by rw [hL]
    _ = 1 := hprod'

private theorem initial_mellin_identity {s : ℂ} (hs : 0 < s.re) :
    s * mobiusMellin s = 1 / riemannZeta (s + 1) :=
  initial_mellin_identity_of_growth weightedMobiusGrowth_proved hs

/-! ## Actual half-line L² Mellin convergence and sharp kernel energy

The following results hold for every complex L² function on the literal
Lebesgue domain (1,∞).  No pointwise bound on that function is used.
-/

private abbrev HalfLineL2 := Lp ℂ 2 halfLineMeasure

def halfLineMellin (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x, f x * (x : ℂ) ^ (-(s + 1)) ∂halfLineMeasure

private def halfLineKernelFn (s : ℂ) (x : ℝ) : ℂ :=
  star ((x : ℂ) ^ (-(s + 1)))

private theorem cpowKernel_aestronglyMeasurable (s : ℂ) :
    AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) halfLineMeasure := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x (-(s + 1))
    (Or.inr (zero_lt_one.trans hx).ne')).continuousWithinAt

private theorem halfLineKernel_norm_sq (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖halfLineKernelFn s x‖ ^ 2 = x ^ (-2 * s.re - 2) := by
  rw [halfLineKernelFn, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  norm_num
  ring

private theorem halfLineKernel_memLp (s : ℂ) (hs : -(1 / 2 : ℝ) < s.re) :
    MemLp (halfLineKernelFn s) 2 halfLineMeasure := by
  have hm := (cpowKernel_aestronglyMeasurable s).star
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hi : IntegrableOn (fun x : ℝ => x ^ (-2 * s.re - 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (halfLineKernel_norm_sq s (zero_lt_one.trans hx)).symm

private def halfLineKernel (s : ℂ) (hs : -(1 / 2 : ℝ) < s.re) : HalfLineL2 :=
  (halfLineKernel_memLp s hs).toLp (halfLineKernelFn s)

private theorem halfLineKernel_coe_ae (s : ℂ) (hs : -(1 / 2 : ℝ) < s.re) :
    (halfLineKernel s hs : ℝ → ℂ) =ᵐ[halfLineMeasure] halfLineKernelFn s :=
  MemLp.coeFn_toLp _

private theorem halfLine_pairing_ae {f : ℝ → ℂ} (hf : MemLp f 2 halfLineMeasure)
    (s : ℂ) (hs : -(1 / 2 : ℝ) < s.re) :
    (fun x => inner ℂ (halfLineKernel s hs x) (hf.toLp f x)) =ᵐ[halfLineMeasure]
      fun x => f x * (x : ℂ) ^ (-(s + 1)) := by
  filter_upwards [halfLineKernel_coe_ae s hs, hf.coeFn_toLp] with x hk hfx
  simp [hk, hfx, halfLineKernelFn, RCLike.inner_apply]

private theorem halfLineMellin_integrable {f : ℝ → ℂ} (hf : MemLp f 2 halfLineMeasure)
    {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re) :
    Integrable (fun x => f x * (x : ℂ) ^ (-(s + 1))) halfLineMeasure :=
  (L2.integrable_inner (𝕜 := ℂ) (halfLineKernel s hs) (hf.toLp f)).congr
    (halfLine_pairing_ae hf s hs)

private theorem halfLineMellin_eq_inner {f : ℝ → ℂ} (hf : MemLp f 2 halfLineMeasure)
    {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re) :
    halfLineMellin f s = inner ℂ (halfLineKernel s hs) (hf.toLp f) := by
  rw [L2.inner_def]
  exact (integral_congr_ae (halfLine_pairing_ae hf s hs)).symm

private theorem halfLineKernel_norm_sq_exact (s : ℂ) (hs : -(1 / 2 : ℝ) < s.re) :
    ‖halfLineKernel s hs‖ ^ 2 = 1 / (2 * s.re + 1) := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (halfLineKernel s hs)
      (halfLineKernel s hs))]
  have he : (fun x => RCLike.re (inner ℂ (halfLineKernel s hs x)
      (halfLineKernel s hs x))) =ᵐ[halfLineMeasure]
      fun x : ℝ => x ^ (-2 * s.re - 2) := by
    filter_upwards [halfLineKernel_coe_ae s hs, ae_restrict_mem measurableSet_Ioi]
      with x hk hx
    rw [← @norm_sq_eq_re_inner ℂ, hk,
      halfLineKernel_norm_sq s (zero_lt_one.trans hx)]
  rw [integral_congr_ae he]
  change (∫ x in Ioi (1 : ℝ), x ^ (-2 * s.re - 2)) = _
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  rw [show -2 * s.re - 2 + 1 = -(2 * s.re + 1) by ring]
  have hp : 2 * s.re + 1 ≠ 0 := by linarith
  field_simp [hp]

private theorem halfLineKernel_norm_exact (s : ℂ) (hs : -(1 / 2 : ℝ) < s.re) :
    ‖halfLineKernel s hs‖ = 1 / Real.sqrt (2 * s.re + 1) := by
  have hn := halfLineKernel_norm_sq_exact s hs
  have hp : 0 < 2 * s.re + 1 := by linarith
  have he : (1 / Real.sqrt (2 * s.re + 1)) ^ 2 = 1 / (2 * s.re + 1) := by
    rw [div_pow, Real.sq_sqrt hp.le, one_pow]
  nlinarith [norm_nonneg (halfLineKernel s hs),
    div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (Real.sqrt_nonneg (2 * s.re + 1))]

theorem halfLineMellin_norm_le {f : ℝ → ℂ} (hf : MemLp f 2 halfLineMeasure)
    {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re) :
    ‖halfLineMellin f s‖ ≤ ‖hf.toLp f‖ / Real.sqrt (2 * s.re + 1) := by
  rw [halfLineMellin_eq_inner hf hs]
  calc
    ‖inner ℂ (halfLineKernel s hs) (hf.toLp f)‖ ≤
        ‖halfLineKernel s hs‖ * ‖hf.toLp f‖ := norm_inner_le_norm _ _
    _ = ‖hf.toLp f‖ / Real.sqrt (2 * s.re + 1) := by
      rw [halfLineKernel_norm_exact]
      ring

private theorem mobiusComplex_memLp_of_real
    (hf : MemLp mobiusPartialSum 2 halfLineMeasure) :
    MemLp (fun x => (mobiusPartialSum x : ℂ)) 2 halfLineMeasure :=
  Complex.ofRealCLM.comp_memLp' hf

private theorem mobiusMellin_norm_bound
    (hf : MemLp mobiusPartialSum 2 halfLineMeasure) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ}, -(1 / 2 : ℝ) < s.re →
      ‖mobiusMellin s‖ ≤ C / Real.sqrt (2 * s.re + 1) := by
  let hc := mobiusComplex_memLp_of_real hf
  refine ⟨‖hc.toLp (fun x => (mobiusPartialSum x : ℂ))‖, norm_nonneg _, ?_⟩
  intro s hs
  exact halfLineMellin_norm_le hc hs

/-! ## Holomorphy from L², by an integrable local derivative bound -/

theorem halfLineMellin_differentiableAt {f : ℝ → ℂ}
    (hf : MemLp f 2 halfLineMeasure) {s₀ : ℂ} (hs₀ : -(1 / 2 : ℝ) < s₀.re) :
    DifferentiableAt ℂ (halfLineMellin f) s₀ := by
  let r : ℝ := (s₀.re + 1 / 2) / 4
  let τ : ℝ := s₀.re - 2 * r
  let U : Set ℂ := {z | s₀.re - r < z.re}
  let F : ℂ → ℝ → ℂ := fun z x => f x * (x : ℂ) ^ (-(z + 1))
  let F' : ℂ → ℝ → ℂ := fun z x =>
    -(f x * (x : ℂ) ^ (-(z + 1)) * (Real.log x : ℂ))
  let B : ℝ → ℝ := fun x =>
    r⁻¹ * ‖f x * (x : ℂ) ^ (-((τ : ℂ) + 1))‖
  have hr : 0 < r := by dsimp [r]; linarith
  have hτ : -(1 / 2 : ℝ) < (τ : ℂ).re := by
    simp only [Complex.ofReal_re]
    dsimp [τ, r]
    linarith
  have hU : U ∈ 𝓝 s₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      change s₀.re - r < s₀.re
      linarith)
  have hFmeas : ∀ᶠ z in 𝓝 s₀, AEStronglyMeasurable (F z) halfLineMeasure := by
    exact Filter.Eventually.of_forall fun z =>
      hf.aestronglyMeasurable.mul (cpowKernel_aestronglyMeasurable z)
  have hFint : Integrable (F s₀) halfLineMeasure := halfLineMellin_integrable hf hs₀
  have hlog : AEStronglyMeasurable (fun x : ℝ => (Real.log x : ℂ))
      halfLineMeasure :=
    (Complex.continuous_ofReal.measurable.comp Real.measurable_log).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' s₀) halfLineMeasure :=
    ((hf.aestronglyMeasurable.mul (cpowKernel_aestronglyMeasurable s₀)).mul hlog).neg
  have hB : Integrable B halfLineMeasure :=
    (halfLineMellin_integrable hf hτ).norm.const_mul r⁻¹
  have hbound : ∀ᵐ x ∂halfLineMeasure, ∀ z ∈ U, ‖F' z x‖ ≤ B x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hlog_le : Real.log x ≤ x ^ r / r := Real.log_le_rpow_div hx0.le hr
    have he : -(z.re + 1) + r ≤ -(τ + 1) := by
      change s₀.re - r < z.re at hz
      dsimp [τ]
      linarith
    have hk : x ^ (-(z.re + 1)) * Real.log x ≤ r⁻¹ * x ^ (-(τ + 1)) := by
      calc
        x ^ (-(z.re + 1)) * Real.log x ≤
            x ^ (-(z.re + 1)) * (x ^ r / r) :=
          mul_le_mul_of_nonneg_left hlog_le (Real.rpow_nonneg hx0.le _)
        _ = x ^ (-(z.re + 1) + r) / r := by
          rw [Real.rpow_add hx0]
          ring
        _ ≤ x ^ (-(τ + 1)) / r :=
          div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx.le he) hr.le
        _ = r⁻¹ * x ^ (-(τ + 1)) := by ring
    simp only [F', B, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog0, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.neg_re, Complex.add_re, Complex.one_re, Complex.ofReal_re]
    calc
      ‖f x‖ * x ^ (-(z.re + 1)) * Real.log x =
          ‖f x‖ * (x ^ (-(z.re + 1)) * Real.log x) := by ring
      _ ≤ ‖f x‖ * (r⁻¹ * x ^ (-(τ + 1))) :=
        mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ = r⁻¹ * (‖f x‖ * x ^ (-(τ + 1))) := by ring
  have hdiff : ∀ᵐ x ∂halfLineMeasure, ∀ z ∈ U,
      HasDerivAt (fun w => F w x) (F' z x) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z _hz
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    have hd := (((hasDerivAt_id z).add_const 1).neg.const_cpow (Or.inl hxne)).const_mul
      (f x)
    simpa [F, F', Complex.ofReal_log hx0.le, mul_assoc, mul_comm, mul_left_comm] using hd
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hU hFmeas hFint hF'meas hbound hB hdiff).2.differentiableAt

theorem halfLineMellin_analyticOnNhd {f : ℝ → ℂ}
    (hf : MemLp f 2 halfLineMeasure) :
    AnalyticOnNhd ℂ (halfLineMellin f) {s : ℂ | -(1 / 2 : ℝ) < s.re} :=
  (show DifferentiableOn ℂ (halfLineMellin f) {s : ℂ | -(1 / 2 : ℝ) < s.re} from
    fun _s hs => (halfLineMellin_differentiableAt hf hs).differentiableWithinAt).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)

private theorem mobiusMellin_analyticOnNhd
    (hf : MemLp mobiusPartialSum 2 halfLineMeasure) :
    AnalyticOnNhd ℂ mobiusMellin {s : ℂ | -(1 / 2 : ℝ) < s.re} :=
  halfLineMellin_analyticOnNhd (mobiusComplex_memLp_of_real hf)

/-! ## Unconditional zero witness and the analytic continuation contract -/

private def puncturedHalfPlane : Set ℂ :=
  {s : ℂ | -(1 / 2 : ℝ) < s.re ∧ s ≠ 0}

private def mellinProductFactor (s : ℂ) : ℂ := s * riemannZeta (s + 1)

private theorem puncturedHalfPlane_isOpen : IsOpen puncturedHalfPlane :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne

/-- Transport the existing punctured right-half-plane connectedness proof.
`isPathConnected_aux` is the port in ZetaBoundsUpper.lean, attributed there
to PrimeNumberTheoremAnd/ZetaBounds.lean and anthropics/zeta-23-lean.
The affine map sends the excluded point 1 to 0 and the boundary to Re=-1/2. -/
private theorem puncturedHalfPlane_isPreconnected : IsPreconnected puncturedHalfPlane := by
  let T : ℂ → ℂ := fun z => (z - 1) / 2
  have hT : Continuous T := by fun_prop
  have hreT : ∀ z : ℂ, (T z).re = (z.re - 1) / 2 := by
    intro z
    norm_num [T, Complex.div_re]
  have himage : T '' {z : ℂ | z ≠ 1 ∧ 0 < z.re} = puncturedHalfPlane := by
    ext s
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hreT]
        linarith [hz.2]
      · exact div_ne_zero (sub_ne_zero.mpr hz.1) (by norm_num)
    · intro hs
      refine ⟨2 * s + 1, ⟨?_, ?_⟩, ?_⟩
      · intro h
        apply hs.2
        linear_combination h / 2
      · simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat,
          Complex.im_ofNat, zero_mul, sub_zero, Complex.one_re]
        linarith [hs.1]
      · dsimp [T]
        ring
  rw [← himage]
  exact isPathConnected_aux.isConnected.isPreconnected.image T hT.continuousOn

private theorem mellinProductFactor_differentiableAt {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ mellinProductFactor s := by
  have hs1 : s + 1 ≠ 1 := by
    intro h
    apply hs
    linear_combination h
  exact differentiableAt_id.mul
    ((differentiableAt_riemannZeta hs1).comp s (differentiableAt_id.add_const 1))

private theorem mellinProductFactor_analyticOnNhd :
    AnalyticOnNhd ℂ mellinProductFactor puncturedHalfPlane :=
  (show DifferentiableOn ℂ mellinProductFactor puncturedHalfPlane from
    fun _s hs => (mellinProductFactor_differentiableAt hs.2).differentiableWithinAt).analyticOnNhd
      puncturedHalfPlane_isOpen

private theorem initial_product {s : ℂ} (hs : 0 < s.re) :
    mellinProductFactor s * mobiusMellin s = 1 := by
  have hz : riemannZeta (s + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  calc
    mellinProductFactor s * mobiusMellin s =
        riemannZeta (s + 1) * (s * mobiusMellin s) := by
      unfold mellinProductFactor
      ring
    _ = riemannZeta (s + 1) * (1 / riemannZeta (s + 1)) := by
      rw [initial_mellin_identity hs]
    _ = 1 := by field_simp

/-- Continue the PRODUCT, never the reciprocal, and never across the excluded
point 0.  In particular this says nothing about the raw totalized value ζ(1). -/
private theorem product_on_punctured
    (hf : MemLp mobiusPartialSum 2 halfLineMeasure) :
    ∀ {s : ℂ}, s ∈ puncturedHalfPlane →
      mellinProductFactor s * mobiusMellin s = 1 := by
  have hM : AnalyticOnNhd ℂ mobiusMellin puncturedHalfPlane :=
    (mobiusMellin_analyticOnNhd hf).mono (fun _ hs => hs.1)
  have hP : AnalyticOnNhd ℂ (fun s => mellinProductFactor s * mobiusMellin s)
      puncturedHalfPlane := mellinProductFactor_analyticOnNhd.mul hM
  have h1 : (1 : ℂ) ∈ puncturedHalfPlane := by
    constructor <;> norm_num
  have heq : (fun s => mellinProductFactor s * mobiusMellin s) =ᶠ[𝓝 (1 : ℂ)]
      (fun _ => (1 : ℂ)) := by
    apply Filter.eventually_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by norm_num))
    intro s hs
    exact initial_product hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hP analyticOnNhd_const
    puncturedHalfPlane_isPreconnected h1 heq

/- The zero supplier is unconditional; reflection is used only to orient one
entry into the half-plane `Re ρ ≥ 1/2`. -/
theorem exists_nontrivial_zero_re_ge_half :
    ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 ≤ ρ.re := by
  let Z := zetaZeroData
  let ρ : ℂ := Z.zero 0
  have hρ : IsNontrivialZero ρ := by
    simpa [ρ, Z] using zetaZeroData_isNontrivial 0
  by_cases h : 1 / 2 ≤ ρ.re
  · exact ⟨ρ, hρ, h⟩
  · have hlt : ρ.re < 1 / 2 := lt_of_not_ge h
    refine ⟨Z.zero (Z.reflection 0), zetaZeroData_isNontrivial (Z.reflection 0), ?_⟩
    rw [Z.zero_reflection]
    simp only [sub_re, one_re]
    linarith

/-! ## The strict boundary growth contradiction

An analytic zero is at least first order in the sense of a local O(distance)
estimate, whether or not it is simple.  Together with the L² O(δ^(-1/2))
bound, this gives a vanishing product.  The proof uses differentiability only;
no derivative is asserted to be nonzero.
-/

private theorem boundary_product_tendsto_zero_of_norm_bound
    {M : ℂ → ℂ} {s₀ : ℂ} (hline : s₀.re = -(1 / 2 : ℝ))
    (hs₀ : s₀ ≠ 0) (hzero : mellinProductFactor s₀ = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ {s : ℂ}, s ∈ puncturedHalfPlane →
      ‖M s‖ ≤ C / Real.sqrt (2 * s.re + 1)) :
    Tendsto (fun δ : ℝ => mellinProductFactor (s₀ + δ) * M (s₀ + δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  have hO : mellinProductFactor =O[𝓝 s₀] (fun s => s - s₀) := by
    simpa only [hzero, sub_zero] using
      (mellinProductFactor_differentiableAt hs₀).isBigO_sub
  obtain ⟨K, hK, hAbound⟩ := isBigO_iff'.mp hO
  have hpath : Tendsto (fun δ : ℝ => s₀ + (δ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s₀) := by
    have ht : Tendsto (fun δ : ℝ => s₀ + (δ : ℂ)) (𝓝 (0 : ℝ)) (𝓝 s₀) := by
      simpa using tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto (0 : ℝ))
    exact ht.mono_left nhdsWithin_le_nhds
  have hprod : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ‖mellinProductFactor (s₀ + δ) * M (s₀ + δ)‖ ≤ K * C * Real.sqrt δ := by
    filter_upwards [hpath.eventually hAbound,
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with δ hAδ hδ
    have hδpos : 0 < δ := hδ.1
    have hsre : (s₀ + δ).re = -(1 / 2 : ℝ) + δ := by
      simp only [Complex.add_re, Complex.ofReal_re, hline]
    have hsne : s₀ + (δ : ℂ) ≠ 0 := by
      intro hs
      have he := congrArg Complex.re hs
      rw [hsre] at he
      norm_num at he
      linarith [hδ.2]
    have hsdom : s₀ + (δ : ℂ) ∈ puncturedHalfPlane := by
      refine ⟨?_, hsne⟩
      rw [hsre]
      linarith
    have hA : ‖mellinProductFactor (s₀ + δ)‖ ≤ K * δ := by
      simpa only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδpos] using hAδ
    have hden : 2 * (s₀ + δ).re + 1 = 2 * δ := by rw [hsre]; ring
    have hMb : ‖M (s₀ + δ)‖ ≤ C / Real.sqrt (2 * δ) := by
      simpa only [hden] using hM hsdom
    have hratio : δ / Real.sqrt (2 * δ) ≤ Real.sqrt δ := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : 0 < 2 * δ))).2
      calc
        δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδpos.le).symm
        _ ≤ Real.sqrt δ * Real.sqrt (2 * δ) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
    calc
      ‖mellinProductFactor (s₀ + δ) * M (s₀ + δ)‖ =
          ‖mellinProductFactor (s₀ + δ)‖ * ‖M (s₀ + δ)‖ := norm_mul _ _
      _ ≤ (K * δ) * (C / Real.sqrt (2 * δ)) :=
        mul_le_mul hA hMb (norm_nonneg _) (mul_nonneg hK.le hδpos.le)
      _ = (K * C) * (δ / Real.sqrt (2 * δ)) := by ring
      _ ≤ K * C * Real.sqrt δ :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hK.le hC)
  have hlim : Tendsto (fun δ : ℝ => K * C * Real.sqrt δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : Continuous (fun δ : ℝ => K * C * Real.sqrt δ) :=
      continuous_const.mul Real.continuous_sqrt
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm' hprod hlim

private theorem boundary_product_tendsto_zero
    (hf : MemLp mobiusPartialSum 2 halfLineMeasure)
    {ρ : ℂ} (hρ : IsNontrivialZero ρ) (hline : ρ.re = 1 / 2) :
    Tendsto (fun δ : ℝ => mellinProductFactor (ρ - 1 + δ) * mobiusMellin (ρ - 1 + δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  obtain ⟨C, hC, hbound⟩ := mobiusMellin_norm_bound hf
  have hs₀ : ρ - 1 ≠ 0 := by
    intro hs
    have he := congrArg Complex.re hs
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re, hline] at he
    norm_num at he
  have hfactor : mellinProductFactor (ρ - 1) = 0 := by
    have hz : riemannZeta ρ = 0 := by
      simpa [D5.S3.Weil.Convention.classicalZeta] using hρ.1
    simp [mellinProductFactor, sub_add_cancel, hz]
  exact boundary_product_tendsto_zero_of_norm_bound
    (by simp only [Complex.sub_re, Complex.one_re, hline]; norm_num)
    hs₀ hfactor hC (by intro s hs; exact hbound hs.1)

/-- The literal weighted Möbius partial sum is unconditionally outside L² on (1,∞).
The proof uses an unconditional nontrivial zero, with separate strict and boundary cases. -/
theorem mobiusPartialSum_not_memLp :
    ¬ MemLp mobiusPartialSum 2 (volume.restrict (Ioi (1 : ℝ))) := by
  intro hf
  obtain ⟨ρ, hρ, hhalf⟩ := exists_nontrivial_zero_re_ge_half
  by_cases hstrict : 1 / 2 < ρ.re
  · let s₀ : ℂ := ρ - 1
    have hs₀_ne : s₀ ≠ 0 := by
      intro hs
      have : ρ = 1 := by
        dsimp [s₀] at hs
        exact sub_eq_zero.mp hs
      have hre : ρ.re = 1 := by simpa [this]
      linarith [hρ.2.2]
    have hs₀_dom : s₀ ∈ puncturedHalfPlane := by
      refine ⟨?_, hs₀_ne⟩
      dsimp [s₀]
      change -(1 / 2 : ℝ) < ρ.re - 1
      linarith
    have hzero : riemannZeta ρ = 0 := by
      simpa [D5.S3.Weil.Convention.classicalZeta] using hρ.1
    have hfactor : mellinProductFactor s₀ = 0 := by
      dsimp [mellinProductFactor, s₀]
      have heq : ρ - 1 + 1 = ρ := by ring
      rw [heq, hzero, mul_zero]
    have hone := product_on_punctured hf hs₀_dom
    rw [hfactor] at hone
    exact (zero_ne_one : (0 : ℂ) ≠ (1 : ℂ)) (by simpa using hone)
  · have hline : ρ.re = 1 / 2 := le_antisymm (le_of_not_gt hstrict) hhalf
    have hzero := boundary_product_tendsto_zero hf hρ hline
    let F : ℝ → ℂ := fun δ : ℝ =>
      mellinProductFactor (ρ - 1 + δ) * mobiusMellin (ρ - 1 + δ)
    have hFzero : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa [F] using hzero
    have hFeq : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), F δ = 1 := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with δ hδ
      have hδpos : 0 < δ := hδ.1
      have hsδre : (ρ - 1 + δ).re < 0 := by
        simp only [add_re, sub_re, one_re, Complex.ofReal_re, hline]
        linarith [hδ.2]
      have hsδ_ne : ρ - 1 + δ ≠ 0 := by
        intro hsδ
        rw [hsδ] at hsδre
        simp at hsδre
      have hsδ_dom : ρ - 1 + δ ∈ puncturedHalfPlane := by
        refine ⟨?_, hsδ_ne⟩
        simp only [add_re, sub_re, one_re, Complex.ofReal_re, hline]
        linarith [hδpos]
      exact product_on_punctured hf hsδ_dom
    have hFone : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      exact tendsto_const_nhds.congr'
        (hFeq.mono fun δ hδ => hδ.symm)
    have h01 : (0 : ℂ) = 1 := tendsto_nhds_unique hFzero hFone
    exact zero_ne_one h01

end D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
