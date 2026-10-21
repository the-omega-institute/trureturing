/- GID: D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/LatticeBoundary
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Actual far images and the full Ioc boundary limit. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.CornerTransport
import D5.S3.Weil.ZetaGamma.GammaMu
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open scoped ComplexConjugate FourierTransform ENNReal Topology ContDiff Classical
open scoped SchwartzMap NNReal Convolution Pointwise

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

open Filter
open scoped Topology ComplexConjugate

private def farRatio (a : ℝ) : ℝ := Real.exp (-a)
private def farDenominator (a : ℝ) : ℝ := 1 - Real.exp (-4 * a)
private def farWeight (a : ℝ) (n : ℕ) : ℝ :=
  (farRatio a / farDenominator a) * farRatio a ^ n
private def actualCtail (a : ℝ) : ℝ :=
  2 * Real.exp (-a) / ((1 - Real.exp (-a)) * (1 - Real.exp (-4 * a)))

private def farDistance (a : ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 - p.2 + ((n : ℝ) + 2) * (2 * a)

private def farCutoffKernel (a ε : ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  if ε < farDistance a n p then actualDensity (farDistance a n p) else 0

private theorem farRatio_pos (a : ℝ) : 0 < farRatio a := Real.exp_pos _
private theorem farRatio_lt_one {a : ℝ} (ha : 0 < a) : farRatio a < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)
private theorem farDenominator_pos {a : ℝ} (ha : 0 < a) :
    0 < farDenominator a := by
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))

private theorem farWeight_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 ≤ farWeight a n :=
  mul_nonneg (div_nonneg (farRatio_pos a).le (farDenominator_pos ha).le)
    (pow_nonneg (farRatio_pos a).le _)

private theorem farWeight_summable {a : ℝ} (ha : 0 < a) :
    Summable (farWeight a) := by
  exact (summable_geometric_of_norm_lt_one (by
    rw [Real.norm_of_nonneg (farRatio_pos a).le]
    exact farRatio_lt_one ha)).mul_left (farRatio a / farDenominator a)

private theorem two_farWeight_tsum {a : ℝ} (ha : 0 < a) :
    2 * (∑' n : ℕ, farWeight a n) = actualCtail a := by
  have hq : ‖farRatio a‖ < 1 := by
    rw [Real.norm_of_nonneg (farRatio_pos a).le]
    exact farRatio_lt_one ha
  rw [show (∑' n : ℕ, farWeight a n) =
      (farRatio a / farDenominator a) * (1 - farRatio a)⁻¹ by
    unfold farWeight
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq]]
  unfold actualCtail farRatio farDenominator
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem actualCtail_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ actualCtail a := by
  rw [← two_farWeight_tsum ha]
  exact mul_nonneg (by norm_num) (tsum_nonneg fun n => farWeight_nonneg ha n)

private theorem farDistance_lower {a : ℝ} {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ((n : ℝ) + 1) * (2 * a) ≤ farDistance a n p := by
  unfold farDistance
  linarith [hx.1, hy.2]

private theorem farDistance_ge_period {a : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    2 * a ≤ farDistance a n p := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have h := farDistance_lower n hx hy
  nlinarith

private theorem actual_far_density_le_weight {a : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualDensity (farDistance a n p) ≤ farWeight a n := by
  have hd := farDistance_ge_period ha n hx hy
  have hden : farDenominator a ≤ 1 - Real.exp (-2 * farDistance a n p) := by
    unfold farDenominator
    exact sub_le_sub_left (Real.exp_le_exp.mpr (by nlinarith)) 1
  have hexp : Real.exp (-farDistance a n p / 2) ≤
      Real.exp (-(((n : ℝ) + 1) * (2 * a)) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [farDistance_lower n hx hy]
  have hident : Real.exp (-(((n : ℝ) + 1) * (2 * a)) / 2) =
      farRatio a * farRatio a ^ n := by
    rw [show -(((n : ℝ) + 1) * (2 * a)) / 2 = -a + (n : ℝ) * (-a) by ring,
      Real.exp_add, Real.exp_nat_mul]
    rfl
  calc
    _ = Real.exp (-farDistance a n p / 2) /
        (1 - Real.exp (-2 * farDistance a n p)) := rfl
    _ ≤ Real.exp (-(((n : ℝ) + 1) * (2 * a)) / 2) / farDenominator a :=
      div_le_div₀ (Real.exp_pos _).le hexp (farDenominator_pos ha) hden
    _ = farWeight a n := by rw [hident]; unfold farWeight; ring

private theorem farCutoffKernel_nonneg {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    0 ≤ farCutoffKernel a ε n p := by
  unfold farCutoffKernel
  split_ifs
  · exact (actual_density_pos (lt_of_lt_of_le (by linarith : 0 < 2 * a)
      (farDistance_ge_period ha n hx hy))).le
  · exact le_rfl

private theorem farCutoffKernel_le_weight {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    farCutoffKernel a ε n p ≤ farWeight a n := by
  unfold farCutoffKernel
  split_ifs
  · exact actual_far_density_le_weight ha n hx hy
  · exact farWeight_nonneg ha n

private theorem farCutoffKernel_summable {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Summable (fun n : ℕ => farCutoffKernel a ε n p) := by
  apply (farWeight_summable ha).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (farCutoffKernel_nonneg ha n hx hy)]
  exact farCutoffKernel_le_weight ha n hx hy

private def actualFarKernel (a ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (∑' n : ℕ, farCutoffKernel a ε n p) +
    ∑' n : ℕ, farCutoffKernel a ε n p.swap

private theorem actualFarKernel_nonneg {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    0 ≤ actualFarKernel a ε p := by
  exact add_nonneg (tsum_nonneg fun n => farCutoffKernel_nonneg ha n hx hy)
    (tsum_nonneg fun n => farCutoffKernel_nonneg ha n hy hx)

private theorem actualFarKernel_le_Ctail {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualFarKernel a ε p ≤ actualCtail a := by
  calc
    _ ≤ (∑' n : ℕ, farWeight a n) + ∑' n : ℕ, farWeight a n := by
      exact add_le_add
        ((farCutoffKernel_summable ha hx hy).tsum_le_tsum
          (fun n => farCutoffKernel_le_weight ha n hx hy) (farWeight_summable ha))
        ((farCutoffKernel_summable ha hy hx).tsum_le_tsum
          (fun n => farCutoffKernel_le_weight ha n hy hx) (farWeight_summable ha))
    _ = actualCtail a := by rw [← two_mul, two_farWeight_tsum ha]

private theorem actualFarKernel_eq_of_small {a ε : ℝ} (ha : 0 < a)
    (hε : ε < 2 * a) {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualFarKernel a ε p = actualFarKernel a 0 p := by
  have hmask (n : ℕ) {q : ℝ × ℝ}
      (hqx : q.1 ∈ Ioo (-a) a) (hqy : q.2 ∈ Ioo (-a) a) :
      farCutoffKernel a ε n q = farCutoffKernel a 0 n q := by
    have hd := farDistance_ge_period ha n hqx hqy
    simp [farCutoffKernel, lt_of_lt_of_le hε hd,
      lt_of_lt_of_le (by linarith : 0 < 2 * a) hd]
  unfold actualFarKernel
  congr 1 <;> apply tsum_congr <;> intro n
  · exact hmask n hx hy
  · exact hmask n hy hx

end D5.S3.Weil.ZetaGamma.FormCore.Corner

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

open Filter
open scoped Topology ComplexConjugate

private theorem intervalMeasure_mass (a : ℝ) (ha : 0 < a) :
    (intervalMeasure a).real univ = 2 * a := by
  have hsub : a - -a = 2 * a := by ring
  simp [intervalMeasure, measureReal_def, Real.volume_Ioo, hsub, ha.le]

private theorem interval_L1_le_sqrt_energy (a : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a)) :
    (∫ x, ‖u x‖ ∂intervalMeasure a) ≤
      Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) * Real.sqrt (2 * a) := by
  have hU : MemLp u (ENNReal.ofReal (2 : ℝ)) (intervalMeasure a) := by
    simpa using hu
  have hOne : MemLp (fun _ : ℝ => (1 : ℂ))
      (ENNReal.ofReal (2 : ℝ)) (intervalMeasure a) := memLp_const _
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hU hOne
  simpa only [norm_one, mul_one, Real.rpow_two, one_pow, integral_const,
    smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow, intervalMeasure_mass a ha] using hHolder

private def normProduct (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ * ‖v p.2‖

private theorem normProduct_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (normProduct u v) ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hu).norm.mul_prod
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hv).norm

private theorem normProduct_integral_le (a : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    (∫ p, normProduct u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      (2 * a) * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  change (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖
      ∂(intervalMeasure a).prod (intervalMeasure a)) ≤ _
  rw [integral_prod_mul (fun x : ℝ => ‖u x‖) (fun y : ℝ => ‖v y‖)]
  calc
    _ ≤ (Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) * Real.sqrt (2 * a)) *
        (Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) * Real.sqrt (2 * a)) :=
      mul_le_mul (interval_L1_le_sqrt_energy a ha hu)
        (interval_L1_le_sqrt_energy a ha hv)
        (integral_nonneg fun y => norm_nonneg (v y))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = (Real.sqrt (2 * a)) ^ 2 *
        Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by ring
    _ = _ := by rw [Real.sq_sqrt (by linarith : 0 ≤ 2 * a)]

private def actualFarPair (a ε : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (actualFarKernel a ε p : ℂ) * v p.2

private theorem actualFarKernel_measurable (a ε : ℝ) :
    Measurable (actualFarKernel a ε) := by
  have hTerm (n : ℕ) : Measurable (farCutoffKernel a ε n) := by
    have hd : Measurable (farDistance a n) := by unfold farDistance; fun_prop
    unfold farCutoffKernel
    exact Measurable.ite (measurableSet_lt measurable_const hd)
      (actual_density_measurable.comp hd) measurable_const
  exact (Measurable.tsum hTerm).add
    (Measurable.tsum fun n => (hTerm n).comp measurable_swap)

private theorem actualFarPair_aestronglyMeasurable (a ε : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (actualFarPair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (actualFarKernel a ε p : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (actualFarKernel_measurable a ε).aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hK).mul
    hv.aestronglyMeasurable.comp_snd

private theorem actualFarPair_norm_le {a ε : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖actualFarPair a ε u v p‖ ≤ actualCtail a * normProduct u v p := by
  unfold actualFarPair
  rw [norm_mul, norm_mul, Complex.norm_conj,
    Complex.norm_of_nonneg (actualFarKernel_nonneg ha hx hy)]
  calc
    _ ≤ ‖u p.1‖ * actualCtail a * ‖v p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (actualFarKernel_le_Ctail ha hx hy)
          (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by unfold normProduct; ring

private theorem actualFarPair_integrable_and_le (a ε : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (actualFarPair a ε u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, ‖actualFarPair a ε u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      actualCtail a * ((2 * a) * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) := by
  have hDom := (normProduct_integrable a hu hv).const_mul (actualCtail a)
  have hLe : ∀ᵐ p ∂(intervalMeasure a).prod (intervalMeasure a),
      ‖actualFarPair a ε u v p‖ ≤ actualCtail a * normProduct u v p := by
    filter_upwards [interval_product_membership a] with p hp
    exact actualFarPair_norm_le ha hp.1 hp.2
  have hInt := hDom.mono' (actualFarPair_aestronglyMeasurable a ε hu hv) hLe
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ p, actualCtail a * normProduct u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) :=
      integral_mono_ae hInt.norm hDom hLe
    _ = actualCtail a * ∫ p, normProduct u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (normProduct_integral_le a ha hu hv)
      (actualCtail_nonneg ha)

private theorem actualFarPair_eq_of_small {a ε : ℝ} (ha : 0 < a)
    (hε : ε < 2 * a) {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualFarPair a ε u v p = actualFarPair a 0 u v p := by
  unfold actualFarPair
  rw [actualFarKernel_eq_of_small ha hε hx hy]

end D5.S3.Weil.ZetaGamma.FormCore.Corner

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

open Filter
open scoped Topology ComplexConjugate

private def integerImageTerm (a ε : ℝ) (m : ℤ) (p : ℝ × ℝ) : ℝ :=
  if m = 0 then 0 else
    if ε < |p.1 - p.2 + m • (2 * a)| then
      actualDensity |p.1 - p.2 + m • (2 * a)| else 0

private def integerImageKernel (a ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑' m : ℤ, integerImageTerm a ε m p

private def integerImagePair (a ε : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (integerImageKernel a ε p : ℂ) * v p.2

private theorem integerImageTerm_pos_far {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε ((n + 2 : ℕ) : ℤ) p = farCutoffKernel a ε n p := by
  have hn : ((n + 2 : ℕ) : ℤ) ≠ 0 := by omega
  have hd : 0 < farDistance a n p :=
    lt_of_lt_of_le (by linarith : 0 < 2 * a) (farDistance_ge_period ha n hx hy)
  have harg : p.1 - p.2 + ((n + 2 : ℕ) : ℤ) • (2 * a) =
      farDistance a n p := by
    simp [farDistance, zsmul_eq_mul, Nat.cast_add]
  simp only [integerImageTerm, hn, ↓reduceIte, harg, abs_of_pos hd, farCutoffKernel]

private theorem integerImageTerm_neg_far {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε (-((n + 2 : ℕ) : ℤ)) p =
      farCutoffKernel a ε n p.swap := by
  have hn : -((n + 2 : ℕ) : ℤ) ≠ 0 := by omega
  have hd : 0 < farDistance a n p.swap :=
    lt_of_lt_of_le (by linarith : 0 < 2 * a) (farDistance_ge_period ha n hy hx)
  have harg : p.1 - p.2 + (-((n + 2 : ℕ) : ℤ)) • (2 * a) =
      -farDistance a n p.swap := by
    simp [farDistance, zsmul_eq_mul, Nat.cast_add]
    ring
  simp only [integerImageTerm, hn, ↓reduceIte, harg, abs_neg, abs_of_pos hd,
    farCutoffKernel]

private theorem integerImageTerm_one {a ε : ℝ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε 1 p =
      if ε < plusDistance a p then actualDensity (plusDistance a p) else 0 := by
  simp only [integerImageTerm, one_ne_zero, ↓reduceIte, one_zsmul]
  change (if ε < |plusDistance a p| then actualDensity |plusDistance a p| else 0) = _
  rw [abs_of_pos (distances_pos hx hy).1]

private theorem integerImageTerm_neg_one {a ε : ℝ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε (-1) p =
      if ε < minusDistance a p then actualDensity (minusDistance a p) else 0 := by
  have harg : p.1 - p.2 + (-1 : ℤ) • (2 * a) = -minusDistance a p := by
    simp only [neg_one_zsmul]
    unfold minusDistance
    ring
  simp only [integerImageTerm, neg_ne_zero.mpr one_ne_zero, ↓reduceIte, harg,
    abs_neg, abs_of_pos (distances_pos hx hy).2]

private theorem integerImageKernel_split {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Summable (fun m : ℤ => integerImageTerm a ε m p) ∧
    integerImageKernel a ε p =
      (if ε < plusDistance a p then actualDensity (plusDistance a p) else 0) +
      (if ε < minusDistance a p then actualDensity (minusDistance a p) else 0) +
      actualFarKernel a ε p := by
  let F : ℤ → ℝ := fun m => integerImageTerm a ε m p
  have hPosTerm (n : ℕ) : F ((n + 2 : ℕ) : ℤ) = farCutoffKernel a ε n p :=
    integerImageTerm_pos_far ha n hx hy
  have hNegTerm (n : ℕ) : F (-(((n + 1 : ℕ) : ℤ) + 1)) =
      farCutoffKernel a ε n p.swap := by
    have hidx : -(((n + 1 : ℕ) : ℤ) + 1) = -((n + 2 : ℕ) : ℤ) := by omega
    rw [hidx]
    exact integerImageTerm_neg_far ha n hx hy
  have hPos : Summable (fun n : ℕ => F (n : ℤ)) := by
    apply Summable.comp_nat_add (k := 2)
    exact (farCutoffKernel_summable ha hx hy).congr fun n => (hPosTerm n).symm
  have hNeg : Summable (fun n : ℕ => F (-((n : ℤ) + 1))) := by
    apply Summable.comp_nat_add (k := 1)
    exact (farCutoffKernel_summable ha hy hx).congr fun n => (hNegTerm n).symm
  have hAll : Summable F := hPos.of_nat_of_neg_add_one hNeg
  have hPosSum : (∑' n : ℕ, F (n : ℤ)) =
      (F 0 + F 1) + ∑' n : ℕ, farCutoffKernel a ε n p := by
    rw [← hPos.sum_add_tsum_nat_add 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.cast_zero, Nat.cast_one, hPosTerm]
  have hNegSum : (∑' n : ℕ, F (-((n : ℤ) + 1))) =
      F (-1) + ∑' n : ℕ, farCutoffKernel a ε n p.swap := by
    rw [hNeg.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add, hNegTerm]
  refine ⟨hAll, ?_⟩
  change (∑' m : ℤ, F m) = _
  rw [tsum_of_nat_of_neg_add_one hPos hNeg, hPosSum, hNegSum]
  have hzero : F 0 = 0 := by simp [F, integerImageTerm]
  have hone := integerImageTerm_one (ε := ε) hx hy
  have hnegone := integerImageTerm_neg_one (ε := ε) hx hy
  change F 1 = _ at hone
  change F (-1) = _ at hnegone
  rw [hzero, hone, hnegone]
  unfold actualFarKernel
  ring

private theorem integerImagePair_split {a ε : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImagePair a ε u v p =
      twoCornerCutoffPair a ε u v p + actualFarPair a ε u v p := by
  unfold integerImagePair
  rw [(integerImageKernel_split ha hx hy).2]
  unfold twoCornerCutoffPair actualFarPair plusPair minusPair
  by_cases hp : ε < plusDistance a p <;>
    by_cases hm : ε < minusDistance a p <;>
      simp [hp, hm] <;> ring

private def fullImageMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  twoCornerMajorant a u v p + actualCtail a * normProduct u v p

private theorem fullImageMajorant_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (fullImageMajorant a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact (twoCornerMajorant_integrable a hu hv).add
    ((normProduct_integrable a hu hv).const_mul (actualCtail a))

private theorem integerImagePair_norm_le {a ε : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖integerImagePair a ε u v p‖ ≤ fullImageMajorant a u v p := by
  rw [integerImagePair_split ha hx hy]
  exact (norm_add_le _ _).trans (add_le_add
    (twoCornerCutoffPair_norm_le hx hy) (actualFarPair_norm_le ha hx hy))

private theorem integerImageKernel_measurable (a ε : ℝ) :
    Measurable (integerImageKernel a ε) := by
  apply Measurable.tsum
  intro m
  unfold integerImageTerm
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte]
    exact measurable_const
  · simp only [hm, ↓reduceIte]
    have hD : Measurable (fun p : ℝ × ℝ => |p.1 - p.2 + m • (2 * a)|) := by
      fun_prop
    exact Measurable.ite (measurableSet_lt measurable_const hD)
      (actual_density_measurable.comp hD) measurable_const

private theorem integerImagePair_aestronglyMeasurable (a ε : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (integerImagePair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (integerImageKernel a ε p : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (integerImageKernel_measurable a ε).aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hK).mul
    hv.aestronglyMeasurable.comp_snd

private theorem integerImagePair_integrable (a ε : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (integerImagePair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  apply (fullImageMajorant_integrable a hu hv).mono'
    (integerImagePair_aestronglyMeasurable a ε hu hv)
  filter_upwards [interval_product_membership a] with p hp
  exact integerImagePair_norm_le ha hp.1 hp.2

private theorem integerImagePair_tendsto {a : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Tendsto (fun ε : ℝ => integerImagePair a ε u v p)
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (integerImagePair a 0 u v p)) := by
  have hd := distances_pos hx hy
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      ε < min (min (plusDistance a p) (minusDistance a p)) (2 * a) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (lt_min (lt_min hd.1 hd.2) (by linarith)))
  apply (tendsto_const_nhds (x := integerImagePair a 0 u v p)).congr'
  filter_upwards [hsmall] with ε hε
  have hp : ε < plusDistance a p := lt_of_lt_of_le hε
    ((min_le_left _ _).trans (min_le_left _ _))
  have hm : ε < minusDistance a p := lt_of_lt_of_le hε
    ((min_le_left _ _).trans (min_le_right _ _))
  have he : ε < 2 * a := lt_of_lt_of_le hε (min_le_right _ _)
  rw [integerImagePair_split ha hx hy, integerImagePair_split ha hx hy,
    actualFarPair_eq_of_small ha he hx hy]
  simp [twoCornerCutoffPair, hp, hm, hd.1, hd.2]

private theorem integerImagePair_integral_tendsto (a : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Tendsto
      (fun ε : ℝ => ∫ p, integerImagePair a ε u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ p, integerImagePair a 0 u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fullImageMajorant a u v)
  · exact Eventually.of_forall fun ε =>
      (integerImagePair_integrable a ε ha hu hv).aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    filter_upwards [interval_product_membership a] with p hp
    exact integerImagePair_norm_le ha hp.1 hp.2
  · exact fullImageMajorant_integrable a hu hv
  · filter_upwards [interval_product_membership a] with p hp
    exact integerImagePair_tendsto ha hp.1 hp.2

end D5.S3.Weil.ZetaGamma.FormCore.Corner

namespace D5.S3.Weil.ZetaGamma.FormCore.Corner

open Filter
open scoped Topology ComplexConjugate

def actualIocBoundaryPair (a ε : ℝ) (u : ℝ → ℂ) : ℝ :=
  (∫ p : ℝ × ℝ, conj (u p.1) *
    ((∑' m : ℤ, if m = 0 then 0 else
      if ε < |p.1 - p.2 + m • (2 * a)| then
        actualDensity |p.1 - p.2 + m • (2 * a)| else 0) : ℂ) * u p.2
    ∂(volume.restrict (Ioc (-a) a)).prod (volume.restrict (Ioc (-a) a))).re

/-- Uniform cutoff bound on the literal original-Ioc whole image kernel. -/
theorem actualIocBoundaryPair_abs_le (a ε : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    |actualIocBoundaryPair a ε u| ≤
      (2 * gammaCk * Real.pi +
        4 * a * Real.exp (-a) /
          ((1 - Real.exp (-a)) * (1 - Real.exp (-4 * a)))) *
      (∫ x, ‖u x‖ ^ 2 ∂(volume.restrict (Ioc (-a) a))) := by
  have hμ : intervalMeasure a = volume.restrict (Ioc (-a) a) :=
    restrict_Ioo_eq_restrict_Ioc
  have hu' : MemLp u 2 (intervalMeasure a) := by rw [hμ]; exact hu
  have hE : 0 ≤ ∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hmajorant :
      (∫ p, fullImageMajorant a u u p
        ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      (2 * gammaCk * Real.pi + 2 * a * actualCtail a) *
        (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) := by
    calc
      _ = (∫ p, twoCornerMajorant a u u p
            ∂(intervalMeasure a).prod (intervalMeasure a)) +
          actualCtail a * (∫ p, normProduct u u p
            ∂(intervalMeasure a).prod (intervalMeasure a)) := by
        simp only [fullImageMajorant,
          integral_add (twoCornerMajorant_integrable a hu' hu')
            ((normProduct_integrable a hu' hu').const_mul (actualCtail a)),
          integral_const_mul]
      _ ≤ 2 * gammaCk * Real.pi *
            Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
            Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) +
          actualCtail a * ((2 * a) *
            Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
            Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a)) :=
        add_le_add (twoCornerMajorant_integral_le a hu' hu')
          (mul_le_mul_of_nonneg_left (normProduct_integral_le a ha hu' hu')
            (actualCtail_nonneg ha))
      _ = (2 * gammaCk * Real.pi + 2 * a * actualCtail a) *
          (Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
            Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hE]
  have hnorm :
      (∫ p, ‖integerImagePair a ε u u p‖
        ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      (2 * gammaCk * Real.pi + 2 * a * actualCtail a) *
        (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) := by
    refine (integral_mono_ae
      (integerImagePair_integrable a ε ha hu' hu').norm
      (fullImageMajorant_integrable a hu' hu') ?_).trans hmajorant
    filter_upwards [interval_product_membership a] with p hp
    exact integerImagePair_norm_le ha hp.1 hp.2
  have hkernel (p : ℝ × ℝ) :
      (integerImageKernel a ε p : ℂ) =
        ∑' m : ℤ, if m = 0 then (0 : ℂ) else
          if ε < |p.1 - p.2 + m • (2 * a)| then
            (actualDensity |p.1 - p.2 + m • (2 * a)| : ℂ) else 0 := by
    unfold integerImageKernel
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    by_cases hm : m = 0
    · simp only [integerImageTerm, hm, ↓reduceIte, Complex.ofReal_zero]
    · simp only [integerImageTerm, hm, ↓reduceIte]
      split_ifs <;> rfl
  have hbound := (Complex.abs_re_le_norm
    (∫ p, integerImagePair a ε u u p
      ∂(intervalMeasure a).prod (intervalMeasure a))).trans
    ((norm_integral_le_integral_norm _).trans hnorm)
  have hconst : 2 * gammaCk * Real.pi + 2 * a * actualCtail a =
      2 * gammaCk * Real.pi + 4 * a * Real.exp (-a) /
        ((1 - Real.exp (-a)) * (1 - Real.exp (-4 * a))) := by
    unfold actualCtail
    simp only [div_eq_mul_inv]
    ring
  simpa only [actualIocBoundaryPair, integerImagePair, hμ, hkernel, hconst]
    using hbound

private theorem actualIocBoundaryPair_tendsto (a : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    Tendsto (fun ε : ℝ => actualIocBoundaryPair a ε u)
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (actualIocBoundaryPair a 0 u)) := by
  have hμ : intervalMeasure a = volume.restrict (Ioc (-a) a) :=
    restrict_Ioo_eq_restrict_Ioc
  have hu' : MemLp u 2 (intervalMeasure a) := by rw [hμ]; exact hu
  have hkernel (ε : ℝ) (p : ℝ × ℝ) :
      (integerImageKernel a ε p : ℂ) =
        ∑' m : ℤ, if m = 0 then (0 : ℂ) else
          if ε < |p.1 - p.2 + m • (2 * a)| then
            (actualDensity |p.1 - p.2 + m • (2 * a)| : ℂ) else 0 := by
    unfold integerImageKernel
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    by_cases hm : m = 0
    · simp only [integerImageTerm, hm, ↓reduceIte, Complex.ofReal_zero]
    · simp only [integerImageTerm, hm, ↓reduceIte]
      split_ifs <;> rfl
  have hDCT := integerImagePair_integral_tendsto a ha hu' hu'
  have hReal := (Complex.continuous_re.tendsto _).comp hDCT
  simpa only [actualIocBoundaryPair, integerImagePair, hμ, hkernel,
    Function.comp_def] using hReal

theorem actualIocBoundaryPair_nat_tendsto (a : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    Tendsto
      (fun n : ℕ => actualIocBoundaryPair a (1 / ((n : ℝ) + 1)) u)
      atTop (𝓝 (actualIocBoundaryPair a 0 u)) := by
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun n => by change 0 < 1 / ((n : ℝ) + 1); positivity
  exact (actualIocBoundaryPair_tendsto a ha hu).comp hε

end D5.S3.Weil.ZetaGamma.FormCore.Corner
