/- GID: D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/SmoothCutoff
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Constructed smooth cutoff and Gamma commutator estimate. -/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff
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

def actualCutoffEta (a ε x : ℝ) : ℝ :=
  Real.smoothTransition ((x + a) / ε - 1) *
    Real.smoothTransition ((a - x) / ε - 1)

def actualCutoffMask (a ε x : ℝ) : ℝ :=
  if x ∈ Ioo (-a) a then 1 - actualCutoffEta a ε x else 0

theorem actualCutoffEta_contDiff (a ε : ℝ) :
    ContDiff ℝ ∞ (actualCutoffEta a ε) := by
  unfold actualCutoffEta
  fun_prop

theorem actualCutoffEta_range (a ε x : ℝ) :
    0 ≤ actualCutoffEta a ε x ∧ actualCutoffEta a ε x ≤ 1 := by
  have h₁ := Real.smoothTransition.nonneg ((x + a) / ε - 1)
  have h₂ := Real.smoothTransition.nonneg ((a - x) / ε - 1)
  have h₃ := Real.smoothTransition.le_one ((x + a) / ε - 1)
  have h₄ := Real.smoothTransition.le_one ((a - x) / ε - 1)
  refine ⟨mul_nonneg h₁ h₂, ?_⟩
  exact (mul_le_mul_of_nonneg_right h₃ h₂).trans (by simpa using h₄)

theorem actualCutoffMask_measurable (a ε : ℝ) :
    Measurable (actualCutoffMask a ε) := by
  have hη := (actualCutoffEta_contDiff a ε).continuous.measurable
  exact Measurable.ite measurableSet_Ioo (measurable_const.sub hη) measurable_const

theorem actualCutoffMask_range (a ε x : ℝ) :
    0 ≤ actualCutoffMask a ε x ∧ actualCutoffMask a ε x ≤ 1 := by
  have hη := actualCutoffEta_range a ε x
  by_cases hx : x ∈ Ioo (-a) a
  · simp only [actualCutoffMask, if_pos hx]
    constructor <;> linarith
  · simp only [actualCutoffMask, if_neg hx]
    norm_num

private theorem actualCutoffMask_vanish {a ε x : ℝ} (hε : 0 < ε)
    (hleft : 2 * ε ≤ a + x) (hright : 2 * ε ≤ a - x) :
    actualCutoffMask a ε x = 0 := by
  have hx : x ∈ Ioo (-a) a := by constructor <;> linarith
  have hl : 1 ≤ (x + a) / ε - 1 := by
    have h : 2 ≤ (x + a) / ε := (le_div_iff₀ hε).2 (by linarith)
    linarith
  have hr : 1 ≤ (a - x) / ε - 1 := by
    have h : 2 ≤ (a - x) / ε := (le_div_iff₀ hε).2 hright
    linarith
  simp only [actualCutoffMask, if_pos hx, actualCutoffEta,
    Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr, one_mul, sub_self]

private theorem smoothTransition_has_global_abs_bound :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y : ℝ,
      |Real.smoothTransition x - Real.smoothTransition y| ≤ H * |x - y| := by
  obtain ⟨K, hK⟩ :=
    (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) 1) isCompact_Icc
  refine ⟨(K : ℝ), K.coe_nonneg, ?_⟩
  intro x y
  let px := projIcc (0 : ℝ) 1 zero_le_one x
  let py := projIcc (0 : ℝ) 1 zero_le_one y
  have hproj : |(px : ℝ) - (py : ℝ)| ≤ |x - y| := by
    simpa only [px, py, NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] using
      (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one).dist_le_mul x y
  have hcompact : |Real.smoothTransition (px : ℝ) -
      Real.smoothTransition (py : ℝ)| ≤ (K : ℝ) * |(px : ℝ) - (py : ℝ)| := by
    simpa only [Real.dist_eq] using
      hK.dist_le_mul (px : ℝ) px.property (py : ℝ) py.property
  calc
    |Real.smoothTransition x - Real.smoothTransition y| =
        |Real.smoothTransition (px : ℝ) - Real.smoothTransition (py : ℝ)| := by
      simp only [px, py, Real.smoothTransition.projIcc]
    _ ≤ (K : ℝ) * |(px : ℝ) - (py : ℝ)| := hcompact
    _ ≤ (K : ℝ) * |x - y| := mul_le_mul_of_nonneg_left hproj K.coe_nonneg

private theorem cutoff_product_abs_bound {A B C D : ℝ}
    (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) :
    |A * B - C * D| ≤ |A - C| + |B - D| := by
  calc
    |A * B - C * D| = |(A - C) * B + C * (B - D)| := by congr 1 <;> ring
    _ ≤ |(A - C) * B| + |C * (B - D)| := abs_add_le _ _
    _ = |A - C| * B + C * |B - D| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hB₀, abs_of_nonneg hC₀]
    _ ≤ |A - C| * 1 + 1 * |B - D| :=
      add_le_add (mul_le_mul_of_nonneg_left hB₁ (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hC₁ (abs_nonneg _))
    _ = |A - C| + |B - D| := by ring

private theorem actualCutoffEta_abs_bound {H : ℝ}
    (hθ : ∀ x y : ℝ, |Real.smoothTransition x - Real.smoothTransition y| ≤
      H * |x - y|) {a ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |actualCutoffEta a ε x - actualCutoffEta a ε y| ≤
      (2 * H / ε) * |x - y| := by
  have hplus : |((x + a) / ε - 1) - ((y + a) / ε - 1)| = |x - y| / ε := by
    rw [show ((x + a) / ε - 1) - ((y + a) / ε - 1) = (x - y) / ε by ring]
    rw [abs_div, abs_of_pos hε]
  have hminus : |((a - x) / ε - 1) - ((a - y) / ε - 1)| = |x - y| / ε := by
    rw [show ((a - x) / ε - 1) - ((a - y) / ε - 1) = (y - x) / ε by ring]
    rw [abs_div, abs_of_pos hε, abs_sub_comm y x]
  have hp := hθ ((x + a) / ε - 1) ((y + a) / ε - 1)
  have hm := hθ ((a - x) / ε - 1) ((a - y) / ε - 1)
  rw [hplus] at hp
  rw [hminus] at hm
  calc
    |actualCutoffEta a ε x - actualCutoffEta a ε y| ≤
        |Real.smoothTransition ((x + a) / ε - 1) -
          Real.smoothTransition ((y + a) / ε - 1)| +
        |Real.smoothTransition ((a - x) / ε - 1) -
          Real.smoothTransition ((a - y) / ε - 1)| :=
      cutoff_product_abs_bound (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)
    _ ≤ H * (|x - y| / ε) + H * (|x - y| / ε) := add_le_add hp hm
    _ = (2 * H / ε) * |x - y| := by ring

private theorem actualCutoffMask_abs_bound {H : ℝ}
    (hθ : ∀ x y : ℝ, |Real.smoothTransition x - Real.smoothTransition y| ≤
      H * |x - y|) {a ε x y : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ioo (-a) a) (hy : y ∈ Ioo (-a) a) :
    |actualCutoffMask a ε x - actualCutoffMask a ε y| ≤
      (2 * H / ε) * |x - y| := by
  simp only [actualCutoffMask, if_pos hx, if_pos hy]
  rw [show (1 - actualCutoffEta a ε x) - (1 - actualCutoffEta a ε y) =
    -(actualCutoffEta a ε x - actualCutoffEta a ε y) by ring, abs_neg]
  exact actualCutoffEta_abs_bound hθ hε x y

private def cutoffDistance (a y : ℝ) : ℝ := min (a - y) (a + y)

private theorem cutoffDistance_pos {a y : ℝ} (hy : y ∈ Ioo (-a) a) :
    0 < cutoffDistance a y := by
  exact lt_min (sub_pos.mpr hy.2) (by linarith [hy.1])

theorem actualCutoffMask_eventually_zero (a x : ℝ) :
    ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, actualCutoffMask a ε x = 0 := by
  by_cases hx : x ∈ Ioo (-a) a
  · have hd := cutoffDistance_pos hx
    have hsmall : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, ε < cutoffDistance a x / 2 :=
      (eventually_lt_nhds (half_pos hd)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hs
    apply actualCutoffMask_vanish hε
    · have hm := min_le_right (a - x) (a + x)
      change ε < min (a - x) (a + x) / 2 at hs
      linarith
    · have hm := min_le_left (a - x) (a + x)
      change ε < min (a - x) (a + x) / 2 at hs
      linarith
  · exact Eventually.of_forall fun ε => by simp only [actualCutoffMask, if_neg hx]

theorem actualCutoffMask_tendsto_zero (a x : ℝ) :
    Tendsto (fun ε => actualCutoffMask a ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  change ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, (0 : ℝ) = actualCutoffMask a ε x
  filter_upwards [actualCutoffMask_eventually_zero a x] with ε hε
  exact hε.symm

private structure GammaCutoffMaskData (a L : ℝ) where
  mask : ℝ → ℝ → ℝ
  nonneg_L : 0 ≤ L
  measurable : ∀ ε, Measurable (mask ε)
  range : ∀ ε x, 0 ≤ mask ε x ∧ mask ε x ≤ 1
  vanish : ∀ {ε x}, 0 < ε → 2 * ε ≤ a + x → 2 * ε ≤ a - x → mask ε x = 0
  local_abs_bound : ∀ {ε x y}, 0 < ε → x ∈ Ioo (-a) a → y ∈ Ioo (-a) a →
    |mask ε x - mask ε y| ≤ (L / ε) * |x - y|
  pointwise_zero : ∀ x,
    Tendsto (fun ε => mask ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)

private def actualCutoffMaskData {H : ℝ} (hH : 0 ≤ H)
    (hθ : ∀ x y : ℝ, |Real.smoothTransition x - Real.smoothTransition y| ≤
      H * |x - y|) (a : ℝ) : GammaCutoffMaskData a (2 * H) where
  mask := actualCutoffMask a
  nonneg_L := mul_nonneg (by norm_num) hH
  measurable := actualCutoffMask_measurable a
  range := actualCutoffMask_range a
  vanish := actualCutoffMask_vanish
  local_abs_bound := actualCutoffMask_abs_bound hθ
  pointwise_zero := actualCutoffMask_tendsto_zero a

def cutoffRadialGap (b : ℝ → ℝ) (y r : ℝ) : ℝ :=
  actualDensity r * ((b (y + r) - b y) ^ 2 + (b (y - r) - b y) ^ 2)

def cutoffFullGap (b : ℝ → ℝ) (y x : ℝ) : ℝ :=
  actualDensity |x - y| * (b x - b y) ^ 2

private def cutoffEnvelope (δ L r : ℝ) : ℝ :=
  if r ≤ δ / 2 then (32 * gammaCk * L ^ 2 / δ ^ 2) * r else 2 * actualDensity r

def actualExteriorPotential (a y : ℝ) : ℝ :=
  (∫ r in Ioi (a - y), actualDensity r) +
    ∫ r in Ioi (a + y), actualDensity r

private def cutoffConstant (L : ℝ) : ℝ :=
  4 * gammaCk * L ^ 2 + 2 * gammaCk * Real.log 2

theorem actualDensity_tail_integrable_for_cutoff {r : ℝ} (hr : 0 < r) :
    IntegrableOn actualDensity (Ioi r) := by
  exact D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_density_tail_integrable hr

private theorem cutoffRadialGap_measurable {b : ℝ → ℝ} (hb : Measurable b) (y : ℝ) :
    Measurable (cutoffRadialGap b y) := by
  unfold cutoffRadialGap
  exact actual_density_measurable.mul
    ((((hb.comp (measurable_const.add measurable_id)).sub measurable_const).pow_const 2).add
      (((hb.comp (measurable_const.sub measurable_id)).sub measurable_const).pow_const 2))

theorem cutoffRadialGap_nonneg (b : ℝ → ℝ) (y : ℝ) {r : ℝ} (hr : 0 < r) :
    0 ≤ cutoffRadialGap b y r :=
  mul_nonneg (actual_density_pos hr).le (add_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem GammaCutoffMaskData.radial_le_tail {a L : ℝ}
    (M : GammaCutoffMaskData a L) (ε y : ℝ) {r : ℝ} (hr : 0 < r) :
    cutoffRadialGap (M.mask ε) y r ≤ 2 * actualDensity r := by
  have hp₀ := M.range ε (y + r)
  have hm₀ := M.range ε (y - r)
  have hy₀ := M.range ε y
  have hp : (M.mask ε (y + r) - M.mask ε y) ^ 2 ≤ 1 := by
    have h := sq_le_sq' (by linarith : -(1 : ℝ) ≤ M.mask ε (y + r) - M.mask ε y)
      (by linarith : M.mask ε (y + r) - M.mask ε y ≤ 1)
    simpa only [one_pow] using h
  have hm : (M.mask ε (y - r) - M.mask ε y) ^ 2 ≤ 1 := by
    have h := sq_le_sq' (by linarith : -(1 : ℝ) ≤ M.mask ε (y - r) - M.mask ε y)
      (by linarith : M.mask ε (y - r) - M.mask ε y ≤ 1)
    simpa only [one_pow] using h
  unfold cutoffRadialGap
  calc
    _ ≤ actualDensity r * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (actual_density_pos hr).le
    _ = 2 * actualDensity r := mul_comm _ _

private theorem GammaCutoffMaskData.radial_le_linear {a L ε y r : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) (hε : 0 < ε)
    (hr : 0 < r) (hnear : r ≤ cutoffDistance a y / 2) :
    cutoffRadialGap (M.mask ε) y r ≤
      (32 * gammaCk * L ^ 2 / (cutoffDistance a y) ^ 2) * r := by
  let δ := cutoffDistance a y
  have hd : 0 < δ := cutoffDistance_pos hy
  have hL : 0 ≤ L := M.nonneg_L
  have hCk : 0 < gammaCk := gammaCk_pos
  have hdright : δ ≤ a - y := min_le_left _ _
  have hdleft : δ ≤ a + y := min_le_right _ _
  change r ≤ δ / 2 at hnear
  have hyp : y + r ∈ Ioo (-a) a := by constructor <;> linarith
  have hym : y - r ∈ Ioo (-a) a := by constructor <;> linarith
  by_cases hsmall : ε < δ / 4
  · have hyzero : M.mask ε y = 0 := M.vanish hε (by linarith) (by linarith)
    have hpzero : M.mask ε (y + r) = 0 := M.vanish hε (by linarith) (by linarith)
    have hmzero : M.mask ε (y - r) = 0 := M.vanish hε (by linarith) (by linarith)
    have hzero : cutoffRadialGap (M.mask ε) y r = 0 := by
      simp [cutoffRadialGap, hyzero, hpzero, hmzero]
    rw [hzero]
    positivity
  · have hlarge : δ ≤ 4 * ε := by linarith
    have hratio : L / ε ≤ 4 * L / δ := by
      apply (div_le_div_iff₀ hε hd).2
      nlinarith [mul_nonneg M.nonneg_L (sub_nonneg.mpr hlarge)]
    have hp := M.local_abs_bound hε hyp hy
    have hm := M.local_abs_bound hε hym hy
    rw [show (y + r) - y = r by ring, abs_of_pos hr] at hp
    rw [show (y - r) - y = -r by ring, abs_neg, abs_of_pos hr] at hm
    have hbound : (L / ε) * r ≤ 4 * L * r / δ := by
      calc
        (L / ε) * r ≤ (4 * L / δ) * r := mul_le_mul_of_nonneg_right hratio hr.le
        _ = 4 * L * r / δ := by ring
    have hB : 0 ≤ 4 * L * r / δ := by positivity
    have hp₂ : (M.mask ε (y + r) - M.mask ε y) ^ 2 ≤ (4 * L * r / δ) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hB).2 (hp.trans hbound)
    have hm₂ : (M.mask ε (y - r) - M.mask ε y) ^ 2 ≤ (4 * L * r / δ) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hB).2 (hm.trans hbound)
    calc
      cutoffRadialGap (M.mask ε) y r ≤
          (gammaCk / r) * ((M.mask ε (y + r) - M.mask ε y) ^ 2 +
            (M.mask ε (y - r) - M.mask ε y) ^ 2) :=
        mul_le_mul_of_nonneg_right (actual_density_le_gammaCk_div hr)
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ (gammaCk / r) * (2 * (4 * L * r / δ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg gammaCk_pos.le hr.le)
      _ = (32 * gammaCk * L ^ 2 / (cutoffDistance a y) ^ 2) * r := by
        change (gammaCk / r) * (2 * (4 * L * r / δ) ^ 2) =
          (32 * gammaCk * L ^ 2 / δ ^ 2) * r
        field_simp [ne_of_gt hr, ne_of_gt hd]
        <;> ring

private theorem GammaCutoffMaskData.radial_le_envelope {a L ε y r : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) (hε : 0 < ε)
    (hr : 0 < r) :
    cutoffRadialGap (M.mask ε) y r ≤ cutoffEnvelope (cutoffDistance a y) L r := by
  by_cases hnear : r ≤ cutoffDistance a y / 2
  · simpa only [cutoffEnvelope, if_pos hnear] using M.radial_le_linear hy hε hr hnear
  · simpa only [cutoffEnvelope, if_neg hnear] using M.radial_le_tail ε y hr

private theorem cutoffEnvelope_integrable {δ L : ℝ} (hd : 0 < δ) :
    IntegrableOn (cutoffEnvelope δ L) (Ioi 0) := by
  have hR : 0 < δ / 2 := half_pos hd
  have hline : IntervalIntegrable (fun r : ℝ => (32 * gammaCk * L ^ 2 / δ ^ 2) * r)
      volume 0 (δ / 2) := (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hnear : IntegrableOn (cutoffEnvelope δ L) (Ioc 0 (δ / 2)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1 hline).congr_fun
      (fun r hr => by simp only [cutoffEnvelope, if_pos hr.2]) measurableSet_Ioc
  have htail_raw : IntegrableOn (fun r => 2 * actualDensity r) (Ioi (δ / 2)) :=
    (actualDensity_tail_integrable_for_cutoff hR).const_mul 2
  have htail : IntegrableOn (cutoffEnvelope δ L) (Ioi (δ / 2)) := by
    apply IntegrableOn.congr_fun htail_raw _ measurableSet_Ioi
    intro r hr
    have hr' : δ / 2 < r := hr
    simp only [cutoffEnvelope, if_neg (not_le.mpr hr')]
  simpa only [Ioc_union_Ioi_eq_Ioi hR.le] using hnear.union htail

private theorem cutoffEnvelope_integral {δ L : ℝ} (hd : 0 < δ) :
    (∫ r in Ioi 0, cutoffEnvelope δ L r) =
      4 * gammaCk * L ^ 2 + 2 * ∫ r in Ioi (δ / 2), actualDensity r := by
  have hR : 0 < δ / 2 := half_pos hd
  have henv := cutoffEnvelope_integrable (L := L) hd
  have htail : IntegrableOn (cutoffEnvelope δ L) (Ioi (δ / 2)) :=
    henv.mono_set (Ioi_subset_Ioi hR.le)
  have hnear : IntervalIntegrable (cutoffEnvelope δ L) volume 0 (δ / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).2
      (henv.mono_set Ioc_subset_Ioi_self)
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hnear htail
  calc
    (∫ r in Ioi 0, cutoffEnvelope δ L r) =
        (∫ r in (0 : ℝ)..(δ / 2), cutoffEnvelope δ L r) +
          ∫ r in Ioi (δ / 2), cutoffEnvelope δ L r := hsplit.symm
    _ = (∫ r in (0 : ℝ)..(δ / 2), (32 * gammaCk * L ^ 2 / δ ^ 2) * r) +
        2 * ∫ r in Ioi (δ / 2), actualDensity r := by
      congr 1
      · rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hR.le]
        exact setIntegral_congr_fun measurableSet_Ioc fun r hr => by
          simp only [cutoffEnvelope, if_pos hr.2]
      · rw [← integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by
          have hr' : δ / 2 < r := hr
          simp only [cutoffEnvelope, if_neg (not_le.mpr hr')]
    _ = 4 * gammaCk * L ^ 2 + 2 * ∫ r in Ioi (δ / 2), actualDensity r := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      congr 1
      field_simp [ne_of_gt hd]
      <;> ring

private theorem actualDensity_half_tail_le {δ : ℝ} (hd : 0 < δ) :
    (∫ r in Ioi (δ / 2), actualDensity r) ≤
      gammaCk * Real.log 2 + ∫ r in Ioi δ, actualDensity r := by
  have hR : 0 < δ / 2 := half_pos hd
  have hRd : δ / 2 ≤ δ := by linarith
  have hρR := actualDensity_tail_integrable_for_cutoff hR
  have hρd := actualDensity_tail_integrable_for_cutoff hd
  have hρint : IntervalIntegrable actualDensity volume (δ / 2) δ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hRd).2
      (hρR.mono_set Ioc_subset_Ioi_self)
  have hinv_cont : ContinuousOn (fun r : ℝ => gammaCk / r) (Icc (δ / 2) δ) :=
    continuousOn_const.div continuousOn_id fun r hr => ne_of_gt (hR.trans_le hr.1)
  have hinv_int : IntervalIntegrable (fun r : ℝ => gammaCk / r) volume (δ / 2) δ :=
    hinv_cont.intervalIntegrable_of_Icc (μ := volume) hRd
  have hle : (∫ r in (δ / 2)..δ, actualDensity r) ≤
      ∫ r in (δ / 2)..δ, gammaCk / r := by
    apply intervalIntegral.integral_mono_on hRd hρint hinv_int
    intro r hr
    exact actual_density_le_gammaCk_div (hR.trans_le hr.1)
  have hinv : (∫ r in (δ / 2)..δ, gammaCk / r) = gammaCk * Real.log 2 := by
    change (∫ r in (δ / 2)..δ, gammaCk * r⁻¹) = gammaCk * Real.log 2
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hR hd]
    have hquot : δ / (δ / 2) = 2 := by
      field_simp [ne_of_gt hd]
      <;> ring
    rw [hquot]
  rw [hinv] at hle
  have hsplit := intervalIntegral.integral_interval_add_Ioi hρR hρd
  linarith

theorem actualDensity_tail_nonneg {δ : ℝ} (hd : 0 < δ) :
    0 ≤ ∫ r in Ioi δ, actualDensity r :=
  setIntegral_nonneg measurableSet_Ioi fun r hr => (actual_density_pos (hd.trans hr)).le

private theorem actualDensity_distance_tail_le_potential {a y : ℝ}
    (hy : y ∈ Ioo (-a) a) :
    (∫ r in Ioi (cutoffDistance a y), actualDensity r) ≤ actualExteriorPotential a y := by
  have hl : 0 < a + y := by linarith [hy.1]
  have hr : 0 < a - y := sub_pos.mpr hy.2
  rcases le_total (a - y) (a + y) with h | h
  · simp only [cutoffDistance, min_eq_left h, actualExteriorPotential]
    linarith [actualDensity_tail_nonneg hl]
  · simp only [cutoffDistance, min_eq_right h, actualExteriorPotential]
    linarith [actualDensity_tail_nonneg hr]

private theorem GammaCutoffMaskData.radial_integrable_and_le {a L ε y : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) (hε : 0 < ε) :
    IntegrableOn (cutoffRadialGap (M.mask ε) y) (Ioi 0) ∧
      (∫ r in Ioi 0, cutoffRadialGap (M.mask ε) y r) ≤
        cutoffConstant L + 2 * actualExteriorPotential a y := by
  have hd := cutoffDistance_pos hy
  have henv := cutoffEnvelope_integrable (L := L) hd
  have hdom : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ‖cutoffRadialGap (M.mask ε) y r‖ ≤ cutoffEnvelope (cutoffDistance a y) L r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (cutoffRadialGap_nonneg _ y hr)]
    exact M.radial_le_envelope hy hε hr
  have hgap := henv.mono' (cutoffRadialGap_measurable (M.measurable ε) y).aestronglyMeasurable hdom
  refine ⟨hgap, ?_⟩
  have hle : (∫ r in Ioi 0, cutoffRadialGap (M.mask ε) y r) ≤
      ∫ r in Ioi 0, cutoffEnvelope (cutoffDistance a y) L r := by
    apply integral_mono_ae hgap henv
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact M.radial_le_envelope hy hε hr
  rw [cutoffEnvelope_integral hd] at hle
  have hhalf := actualDensity_half_tail_le hd
  have hpot := actualDensity_distance_tail_le_potential hy
  unfold cutoffConstant
  linarith

private theorem GammaCutoffMaskData.radial_tendsto_zero {a L y : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) :
    Tendsto (fun ε => ∫ r in Ioi 0, cutoffRadialGap (M.mask ε) y r)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hd := cutoffDistance_pos hy
  have henv := cutoffEnvelope_integrable (L := L) hd
  have hmeas : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      AEStronglyMeasurable (cutoffRadialGap (M.mask ε) y) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun ε => (cutoffRadialGap_measurable (M.measurable ε) y).aestronglyMeasurable
  have hdom : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
        ‖cutoffRadialGap (M.mask ε) y r‖ ≤ cutoffEnvelope (cutoffDistance a y) L r := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (cutoffRadialGap_nonneg _ y hr)]
    exact M.radial_le_envelope hy hε hr
  have hlim : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun ε => cutoffRadialGap (M.mask ε) y r)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro r
    have hp := ((M.pointwise_zero (y + r)).sub (M.pointwise_zero y)).pow 2
    have hm := ((M.pointwise_zero (y - r)).sub (M.pointwise_zero y)).pow 2
    have hρ : Tendsto (fun _ε : ℝ => actualDensity r)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (actualDensity r)) := tendsto_const_nhds
    simpa [cutoffRadialGap] using hρ.mul (hp.add hm)
  have h := tendsto_integral_filter_of_dominated_convergence
    (cutoffEnvelope (cutoffDistance a y) L) hmeas hdom henv hlim
  simpa only [integral_zero] using h

private theorem cutoffFullGap_integrable_and_radial {b : ℝ → ℝ} (hb : Measurable b)
    (y : ℝ) (hradial : IntegrableOn (cutoffRadialGap b y) (Ioi 0)) :
    Integrable (cutoffFullGap b y) ∧
      (∫ x, cutoffFullGap b y x) = ∫ r in Ioi 0, cutoffRadialGap b y r := by
  let F : ℝ → ℝ := fun r => actualDensity |r| * (b (y + r) - b y) ^ 2
  have hFm : Measurable F :=
    (actual_density_measurable.comp measurable_abs).mul
      (((hb.comp (measurable_const.add measurable_id)).sub measurable_const).pow_const 2)
  have hpositive : IntegrableOn F (Ioi (0 : ℝ)) := by
    apply hradial.mono' hFm.aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr' : 0 < r := hr
    have hρ := (actual_density_pos hr').le
    have hF : F r = actualDensity r * (b (y + r) - b y) ^ 2 := by
      simp only [F, abs_of_pos hr']
    rw [hF, Real.norm_of_nonneg (mul_nonneg hρ (sq_nonneg _))]
    unfold cutoffRadialGap
    nlinarith [mul_nonneg hρ (sq_nonneg (b (y - r) - b y))]
  have hnegative : IntegrableOn (fun r => F (-r)) (Ioi (0 : ℝ)) := by
    apply hradial.mono' (hFm.comp measurable_neg).aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    change ‖F (-r)‖ ≤ cutoffRadialGap b y r
    have hr' : 0 < r := hr
    have hρ := (actual_density_pos hr').le
    have hF : F (-r) = actualDensity r * (b (y - r) - b y) ^ 2 := by
      simp only [F, abs_neg, abs_of_pos hr', ← sub_eq_add_neg]
    rw [hF, Real.norm_of_nonneg (mul_nonneg hρ (sq_nonneg _))]
    unfold cutoffRadialGap
    nlinarith [mul_nonneg hρ (sq_nonneg (b (y + r) - b y))]
  have hleft : IntegrableOn F (Iic (0 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hnegative
  have hF : Integrable F := by
    simpa only [Iic_union_Ioi, IntegrableOn, Measure.restrict_univ] using hleft.union hpositive
  have hfull_meas : Measurable (cutoffFullGap b y) :=
    (actual_density_measurable.comp ((measurable_id.sub measurable_const).abs)).mul
      ((hb.sub measurable_const).pow_const 2)
  have hshift : (fun r => cutoffFullGap b y (r + y)) = F := by
    funext r
    simp only [cutoffFullGap, F]
    rw [add_sub_cancel_right, add_comm r y]
  have hfull : Integrable (cutoffFullGap b y) := by
    apply ((measurePreserving_add_right (volume : Measure ℝ) y).integrable_comp
      hfull_meas.aestronglyMeasurable).mp
    change Integrable (fun r => cutoffFullGap b y (r + y))
    rw [hshift]
    exact hF
  refine ⟨hfull, ?_⟩
  calc
    (∫ x, cutoffFullGap b y x) = ∫ r, F r := by
      rw [← integral_add_right_eq_self (cutoffFullGap b y) y, hshift]
    _ = (∫ r in Iic (0 : ℝ), F r) + ∫ r in Ioi (0 : ℝ), F r :=
      (intervalIntegral.integral_Iic_add_Ioi hleft hpositive).symm
    _ = (∫ r in Ioi (0 : ℝ), F (-r)) + ∫ r in Ioi (0 : ℝ), F r := by
      rw [integral_comp_neg_Ioi, neg_zero]
    _ = ∫ r in Ioi (0 : ℝ), F (-r) + F r := (integral_add hnegative hpositive).symm
    _ = ∫ r in Ioi (0 : ℝ), cutoffRadialGap b y r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr' : 0 < r := hr
      simp only [F, cutoffRadialGap, abs_neg, abs_of_pos hr', ← sub_eq_add_neg]
      ring

theorem actual_smooth_cutoff_commutator :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      (∀ a ε : ℝ, ContDiff ℝ ∞ (actualCutoffEta a ε)) ∧
      ∀ a y : ℝ, y ∈ Ioo (-a) a →
        ((∀ ε : ℝ, 0 < ε →
            IntegrableOn (cutoffRadialGap (actualCutoffMask a ε) y) (Ioi 0) ∧
              (∫ r in Ioi 0, cutoffRadialGap (actualCutoffMask a ε) y r) ≤
                C0 + 2 * actualExteriorPotential a y) ∧
          Tendsto (fun ε => ∫ r in Ioi 0, cutoffRadialGap (actualCutoffMask a ε) y r)
            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) ∧
        ((∀ ε : ℝ, 0 < ε →
            Integrable (cutoffFullGap (actualCutoffMask a ε) y) ∧
              (∫ x, cutoffFullGap (actualCutoffMask a ε) y x) ≤
                C0 + 2 * actualExteriorPotential a y) ∧
          Tendsto (fun ε => ∫ x, cutoffFullGap (actualCutoffMask a ε) y x)
            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) := by
  obtain ⟨H, hH, hθ⟩ := smoothTransition_has_global_abs_bound
  let L := 2 * H
  have hC : 0 ≤ cutoffConstant L := by
    unfold cutoffConstant
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) gammaCk_pos.le) (sq_nonneg L))
      (mul_nonneg (mul_nonneg (by norm_num) gammaCk_pos.le)
        (Real.log_nonneg (by norm_num)))
  refine ⟨cutoffConstant L, hC, actualCutoffEta_contDiff, ?_⟩
  intro a y hy
  let M : GammaCutoffMaskData a L := actualCutoffMaskData hH hθ a
  refine ⟨⟨fun ε hε => M.radial_integrable_and_le hy hε,
    M.radial_tendsto_zero hy⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · intro ε hε
    have hr := M.radial_integrable_and_le hy hε
    have hf := cutoffFullGap_integrable_and_radial (actualCutoffMask_measurable a ε) y hr.1
    refine ⟨hf.1, ?_⟩
    rw [hf.2]
    exact hr.2
  · have hr := M.radial_tendsto_zero hy
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hi := (M.radial_integrable_and_le hy hε).1
    exact (cutoffFullGap_integrable_and_radial
      (actualCutoffMask_measurable a ε) y hi).2.symm

end D5.S3.Weil.ZetaGamma.FormCore.Corner
