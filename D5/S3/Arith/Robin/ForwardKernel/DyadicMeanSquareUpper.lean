/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform short-interval variance bound controls the dyadic mean square of the forward response. -/

import D5.S3.Arith.Robin.ForwardKernel.MellinConvergence
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import D5.S3.Arith.Robin.ForwardKernel.ProfileKernelDefs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.L2Space

/-! Weighted averaging transports the short-interval variance estimate to the forward response. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareUpper

open Set MeasureTheory
open VarianceTransfer (interval_cauchy_schwarz logarithmic_variance_mono)
open VarianceTransferDefs (LocallyBoundedMeasurable)
open OriginalMovingWindowMoment (width weight_pos weight_antitone)
open MellinWeightedVariation (weight)
open ActualVonMangoldtBandCompensation (discrepancy)
open ForwardKernel.Transport (forwardResponse)
open ForwardKernel.MellinConvergence (discrepancy_measurable response_measurable)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The uniform Saffari–Vaughan estimate for the complete Chebyshev error. -/
def ShortIntervalMeanSquareBound : Prop :=
  VarianceTransferDefs.ShortIntervalMeanSquareBoundFor discrepancy

/-- The complete Chebyshev error is measurable and bounded on every finite interval. -/
theorem discrepancy_locallyBoundedMeasurable : LocallyBoundedMeasurable discrepancy := by
  refine ⟨MellinConvergence.discrepancy_measurable, ?_⟩
  intro a b
  refine ⟨Chebyshev.psi b + (|a| + |b|), by positivity [Chebyshev.psi_nonneg b], ?_⟩
  intro x hx
  have hxabs : |x| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b, hx.1]
    · linarith [le_abs_self b, abs_nonneg a, hx.2]
  exact (abs_sub _ _).trans (add_le_add
    (by simpa only [abs_of_nonneg (Chebyshev.psi_nonneg x)] using Chebyshev.psi_mono hx.2)
    hxabs)

private def increment (x θ : ℝ) : ℝ := discrepancy ((1 + θ) * x) - discrepancy x

private lemma increment_measurable : Measurable (fun p : ℝ × ℝ => increment p.1 p.2) := by
  exact (discrepancy_measurable.comp
    ((measurable_const.add measurable_snd).mul measurable_fst)).sub
      (discrepancy_measurable.comp measurable_fst)

private lemma increment_bound {X x θ : ℝ} (hX : 0 < X)
    (hx : x ∈ Icc X (2 * X)) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    |increment x θ| ≤ 2 * (Chebyshev.psi (4 * X) + 4 * X) := by
  have hx0 : 0 ≤ x := hX.le.trans hx.1
  have hy0 : 0 ≤ (1 + θ) * x := by positivity [hθ.1]
  have hy : (1 + θ) * x ≤ 4 * X := by
    nlinarith [mul_le_mul_of_nonneg_right hθ.2 hx0, hx.2]
  have hb (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 4 * X) :
      |discrepancy t| ≤ Chebyshev.psi (4 * X) + 4 * X := by
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (Chebyshev.psi_nonneg t), abs_of_nonneg ht]
      exact add_le_add (Chebyshev.psi_mono ht') ht')
  exact (abs_sub _ _).trans (by linarith [hb x hx0 (by linarith [hx.2]), hb _ hy0 hy])

private lemma increment_square_integrable {X a : ℝ} (hX : 0 < X)
    (_ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Integrable (fun p : ℝ × ℝ => increment p.1 p.2 ^ 2)
      ((volume.restrict (Ioc X (2 * X))).prod (volume.restrict (Ioc (0 : ℝ) a))) := by
  have hmem : ∀ᵐ p ∂((volume.restrict (Ioc X (2 * X))).prod
      (volume.restrict (Ioc (0 : ℝ) a))), p ∈ Ioc X (2 * X) ×ˢ Ioc (0 : ℝ) a := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  refine ⟨(increment_measurable.pow_const 2).aestronglyMeasurable,
    .of_bounded (C := (2 * (Chebyshev.psi (4 * X) + 4 * X)) ^ 2) ?_⟩
  filter_upwards [hmem] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := increment_bound hX ⟨hp.1.1.le, hp.1.2⟩ ⟨hp.2.1.le, hp.2.2.trans ha1⟩
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

private lemma increment_section_integrable {x a : ℝ} (hx : 0 < x)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    IntervalIntegrable (fun θ => increment x θ ^ 2) volume 0 a := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
  refine ⟨((increment_measurable.comp (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable,
    .of_bounded (C := (2 * (Chebyshev.psi (4 * x) + 4 * x)) ^ 2) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := increment_bound hx ⟨le_rfl, by linarith⟩ ⟨hθ.1.le, hθ.2.trans ha1⟩
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

private lemma weighted_section_integrable {x a : ℝ} (hx : 1 < x)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    IntervalIntegrable
      (fun θ => increment x θ * (weight ((1 + θ) * x) / weight x)) volume 0 a ∧
    IntervalIntegrable
      (fun θ => (increment x θ * (weight ((1 + θ) * x) / weight x)) ^ 2) volume 0 a := by
  have hm : Measurable (fun θ => increment x θ * (weight ((1 + θ) * x) / weight x)) := by
    have hw : Measurable weight := by unfold weight; fun_prop
    exact (increment_measurable.comp (measurable_const.prodMk measurable_id)).mul
      ((hw.comp ((measurable_const.add measurable_id).mul_const x)).div_const _)
  have hb (θ : ℝ) (hθ : θ ∈ Ioc (0 : ℝ) a) :
      |increment x θ * (weight ((1 + θ) * x) / weight x)| ≤
        2 * (Chebyshev.psi (4 * x) + 4 * x) := by
    have hx0 : 0 < x := by linarith
    have hy : x ≤ (1 + θ) * x := by nlinarith [hθ.1]
    have hr0 : 0 ≤ weight ((1 + θ) * x) / weight x :=
      div_nonneg (weight_pos (hx.trans_le hy)).le (weight_pos hx).le
    have hr1 : weight ((1 + θ) * x) / weight x ≤ 1 :=
      (div_le_one (weight_pos hx)).mpr (weight_antitone hx hy)
    rw [abs_mul, abs_of_nonneg hr0]
    exact (mul_le_of_le_one_right (abs_nonneg _) hr1).trans
      (increment_bound hx0 ⟨le_rfl, by linarith⟩ ⟨hθ.1.le, hθ.2.trans ha1⟩)
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    refine ⟨hm.aestronglyMeasurable,
      .of_bounded (C := 2 * (Chebyshev.psi (4 * x) + 4 * x)) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    simpa only [Real.norm_eq_abs] using hb θ hθ
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    refine ⟨(hm.pow_const 2).aestronglyMeasurable,
      .of_bounded (C := (2 * (Chebyshev.psi (4 * x) + 4 * x)) ^ 2) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hb θ hθ) 2

private lemma response_theta {x : ℝ} (hx : 0 < x) :
    forwardResponse x = Real.sqrt x * x / width x ^ 2 *
      ∫ θ in (0 : ℝ)..(width x / x),
        increment x θ * (weight ((1 + θ) * x) / weight x) := by
  have hs := intervalIntegral.smul_integral_comp_mul_right
    (fun u => (discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x))
    (a := 0) (b := width x / x) x
  simp only [smul_eq_mul, zero_mul, div_mul_cancel₀ _ hx.ne'] at hs
  have he : (fun θ => (discrepancy (x + θ * x) - discrepancy x) *
      (weight (x + θ * x) / weight x)) =
      (fun θ => increment x θ * (weight ((1 + θ) * x) / weight x)) := by
    funext θ
    simp only [increment, show x + θ * x = (1 + θ) * x by ring]
  rw [he] at hs
  rw [ProfileKernelDefs.forwardResponse_eq_profileResponse]
  simp only [ProfileKernelDefs.profileResponse, ProfileKernelDefs.priceRatio,
    VarianceTransferDefs.increment, one_mul]
  change Real.sqrt x / width x ^ 2 *
    (∫ u in (0 : ℝ)..width x,
      (discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x)) = _
  rw [← hs]
  ring

private lemma response_square_le {x : ℝ} (hx : 1 < x) :
    forwardResponse x ^ 2 / x ≤ x / width x ^ 3 *
      ∫ θ in (0 : ℝ)..(width x / x), increment x θ ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hH : 0 < width x := Real.rpow_pos_of_pos hx0 _
  have ha : 0 < width x / x := div_pos hH hx0
  have ha1 : width x / x ≤ 1 := (div_le_one hx0).mpr
    (Real.rpow_le_self_of_one_le hx.le (by norm_num))
  obtain ⟨hi, hi2⟩ := weighted_section_integrable hx ha.le ha1
  have hcs := interval_cauchy_schwarz ha hi hi2
  have hm : (∫ θ in (0 : ℝ)..(width x / x),
      (increment x θ * (weight ((1 + θ) * x) / weight x)) ^ 2) ≤
      ∫ θ in (0 : ℝ)..(width x / x), increment x θ ^ 2 := by
    apply intervalIntegral.integral_mono_on ha.le hi2
      (increment_section_integrable hx0 ha.le ha1)
    intro θ hθ
    have hy : x ≤ (1 + θ) * x := by nlinarith [hθ.1]
    have hr0 : 0 ≤ weight ((1 + θ) * x) / weight x :=
      div_nonneg (weight_pos (hx.trans_le hy)).le (weight_pos hx).le
    have hr1 : weight ((1 + θ) * x) / weight x ≤ 1 :=
      (div_le_one (weight_pos hx)).mpr (weight_antitone hx hy)
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith :
      (weight ((1 + θ) * x) / weight x) ^ 2 ≤ 1)
  have h := hcs.trans (mul_le_mul_of_nonneg_left hm ha.le)
  rw [response_theta hx0, mul_pow, div_pow, mul_pow, Real.sq_sqrt hx0.le]
  have hs := mul_le_mul_of_nonneg_left h (show 0 ≤ x ^ 2 / width x ^ 4 by positivity)
  convert hs using 1 <;> field_simp

private lemma response_rectangle_le {X a : ℝ} (hX : 1 < X)
    (ha : 0 < a) (ha1 : a ≤ 1) (hXa : X ^ (-1 / 5 : ℝ) ≤ a)
    {x : ℝ} (hx : x ∈ Icc X (2 * X)) :
    forwardResponse x ^ 2 / x ≤ X ^ (-7 / 5 : ℝ) *
      ∫ θ in (0 : ℝ)..a, increment x θ ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hx1 : 1 < x := hX.trans_le hx.1
  have hx0 : 0 < x := by linarith
  have hwidth : 0 ≤ width x / x := div_nonneg (Real.rpow_nonneg hx0.le _) hx0.le
  have hsmall : width x / x ≤ a := by
    have he := Real.rpow_sub hx0 (4 / 5 : ℝ) 1
    norm_num only [Real.rpow_one, show (4 / 5 : ℝ) - 1 = -1 / 5 by norm_num] at he
    change x ^ (4 / 5 : ℝ) / x ≤ a
    rw [← he]
    convert (Real.rpow_le_rpow_of_nonpos hX0 hx.1
      (by norm_num : (-1 / 5 : ℝ) ≤ 0)).trans hXa using 1 <;> norm_num
  have hi := increment_section_integrable hx0 ha.le ha1
  have hmono := intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) hwidth hsmall
    (Filter.Eventually.of_forall (fun θ => sq_nonneg (increment x θ))) hi
  have hfac : x / width x ^ 3 = x ^ (-7 / 5 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) / x ^ ((4 / 5 : ℝ) * 3) := by
        rw [Real.rpow_one, Real.rpow_mul hx0.le]
        norm_num [width]
      _ = x ^ ((1 : ℝ) - (4 / 5 : ℝ) * 3) := (Real.rpow_sub hx0 _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ (x / width x ^ 3) * ∫ θ in (0 : ℝ)..(width x / x), increment x θ ^ 2 :=
      response_square_le hx1
    _ ≤ (x / width x ^ 3) * ∫ θ in (0 : ℝ)..a, increment x θ ^ 2 :=
      mul_le_mul_of_nonneg_left hmono (div_nonneg hx0.le
        (pow_nonneg (Real.rpow_nonneg hx0.le _) _))
    _ ≤ _ := by
      rw [hfac]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hX0 hx.1 (by norm_num))
        (intervalIntegral.integral_nonneg_of_forall ha.le (fun θ => sq_nonneg _))

private lemma rectangle_bound {C X a : ℝ} (hC : 0 < C) (hX : 1 < X)
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) (hXa : X ^ (-1 / 5 : ℝ) ≤ a)
    (hSV : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫ x in X..(2 * X), increment x θ ^ 2) ≤
        C * θ * X ^ 2 * (Real.log (2 / θ)) ^ 2) :
    (∫ x in X..(2 * X), forwardResponse x ^ 2 / x) ≤
      X ^ (-7 / 5 : ℝ) * (C * X ^ 2 * a ^ 2 * (Real.log (2 / a)) ^ 2) := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hi := increment_square_integrable hX0 ha.le ha1
  have hG : IntervalIntegrable (fun x => X ^ (-7 / 5 : ℝ) *
      ∫ θ in (0 : ℝ)..a, increment x θ ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXX]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le ha.le] using
      hi.integral_prod_left.const_mul (X ^ (-7 / 5 : ℝ))
  have hF : IntervalIntegrable (fun x => forwardResponse x ^ 2 / x) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXX] at hG ⊢
    refine hG.mono' ((response_measurable.pow_const 2).div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith [hx.1]))]
    exact response_rectangle_le hX ha ha1 hXa ⟨hx.1.le, hx.2⟩
  have hrect : (∫ x in X..(2 * X), ∫ θ in (0 : ℝ)..a, increment x θ ^ 2) ≤
      C * X ^ 2 * a ^ 2 * (Real.log (2 / a)) ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le hXX, intervalIntegral.integral_of_le ha.le]
    rw [integral_integral_swap hi]
    calc
      _ ≤ ∫ _θ in Ioc (0 : ℝ) a, C * X ^ 2 * (a * (Real.log (2 / a)) ^ 2) := by
        apply setIntegral_mono_on hi.integral_prod_right (integrableOn_const (by simp))
          measurableSet_Ioc
        intro θ hθ
        have h := hSV θ hθ.1 (hθ.2.trans ha1)
        rw [intervalIntegral.integral_of_le hXX] at h
        have hl := logarithmic_variance_mono ⟨hθ.1, hθ.2.trans ha16⟩ ⟨ha, ha16⟩ hθ.2
        exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ C * X ^ 2)])
      _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ a - 0), smul_eq_mul]
        ring
  calc
    _ ≤ ∫ x in X..(2 * X), X ^ (-7 / 5 : ℝ) *
        ∫ θ in (0 : ℝ)..a, increment x θ ^ 2 :=
      intervalIntegral.integral_mono_on hXX hF hG
        (fun x hx => response_rectangle_le hX ha ha1 hXa hx)
    _ = X ^ (-7 / 5 : ℝ) *
        (∫ x in X..(2 * X), ∫ θ in (0 : ℝ)..a, increment x θ ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hrect (Real.rpow_nonneg hX0.le _)

/-- A uniform short-interval variance estimate bounds the dyadic mean square
of the complete forward response; no separate Riemann hypothesis is needed. -/
theorem forward_kernel_dyadic_mean_square_upper
    (hSV : ShortIntervalMeanSquareBound) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      (∫ x in X..(2 * X), forwardResponse x ^ 2 / x) ≤
        C * X ^ (1 / 5 : ℝ) * (Real.log X) ^ 2 := by
  obtain ⟨C, Y, hC, hY, hSV⟩ := hSV
  refine ⟨4 * C, max Y ((16 : ℝ) ^ (5 : ℕ)), by positivity,
    le_trans (by norm_num : (3 : ℝ) ≤ 16 ^ (5 : ℕ)) (le_max_right _ _), ?_⟩
  intro X hX
  have hXY : Y ≤ X := (le_max_left _ _).trans hX
  have hXL : (16 : ℝ) ^ (5 : ℕ) ≤ X := (le_max_right _ _).trans hX
  have hX4 : 4 ≤ X := (by norm_num : (4 : ℝ) ≤ 16 ^ (5 : ℕ)).trans hXL
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  let a : ℝ := X ^ (-1 / 5 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hX0 _
  have ha16 : a ≤ 1 / 16 := by
    have h := Real.rpow_le_rpow_of_nonpos
      (by norm_num : (0 : ℝ) < 16 ^ (5 : ℕ)) hXL (by norm_num : (-1 / 5 : ℝ) ≤ 0)
    have he : ((16 : ℝ) ^ (5 : ℕ)) ^ (-1 / 5 : ℝ) = 1 / 16 := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num
    exact h.trans_eq he
  have hb := rectangle_bound hC hX1 ha ha16 (le_refl a) (by
    intro θ hθ hθ1
    simpa only [increment, discrepancy] using hSV X hXY θ hθ hθ1)
  have hlog0 : 0 ≤ Real.log (2 / a) :=
    Real.log_nonneg ((one_le_div ha).mpr (by linarith))
  have hlog : Real.log (2 / a) ≤ 2 * Real.log X := by
    rw [Real.log_div (by norm_num) ha.ne', show Real.log a =
      (-1 / 5 : ℝ) * Real.log X from Real.log_rpow hX0 _]
    have hl2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
    have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1.le
    linarith
  have hlogsq : (Real.log (2 / a)) ^ 2 ≤ 4 * (Real.log X) ^ 2 := by
    nlinarith [Real.log_nonneg hX1.le]
  have hp : X ^ (-7 / 5 : ℝ) * X ^ (2 : ℕ) * a ^ (2 : ℕ) = X ^ (1 / 5 : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast X 2, ← Real.rpow_natCast (X ^ (-1 / 5 : ℝ)) 2,
      ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    norm_num
  calc
    _ ≤ X ^ (-7 / 5 : ℝ) * (C * X ^ 2 * a ^ 2 * (Real.log (2 / a)) ^ 2) := hb
    _ = C * X ^ (1 / 5 : ℝ) * (Real.log (2 / a)) ^ 2 := by rw [← hp]; ring
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hlogsq
        (show 0 ≤ C * X ^ (1 / 5 : ℝ) by positivity)]

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareUpper
