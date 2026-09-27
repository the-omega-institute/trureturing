/- GID: D5/S3/Constants/Moments/CatalanSquareHankelLimits
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/CatalanSquareHankelLimits
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality]
   utility: none
   digest: Both Kotesovec squared-Catalan Hankel limits equal two times log two. -/

import D5.S3.Constants.Moments.CatalanSquareHankelGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace D5.S3.Constants.Moments.CatalanSquareHankelLimits
open D5.S3.Constants.Moments.CatalanSquareHankelGrowth
open private clippedCatalanProductCoordinate det_gram_monic_polynomial_change productShiftOneLpVector
  productShiftTwoLpVector productShiftOneGramVector productShiftTwoGramVector
  catalanSquareHankelMatrix_eq_product_gram_one catalanSquareHankelMatrix_eq_product_gram_two from
  D5.S3.Constants.Moments.CatalanSquareHankelGrowth
private local instance : IsProbabilityMeasure catalanBetaMeasure := by
  rw [catalanBetaMeasure]; exact isProbabilityMeasureBeta (by norm_num) (by norm_num)
private def literalProductEnergy (r : Nat) (P : Polynomial Real) (p : Real × Real) : Real :=
  (16 * p.1 * p.2) ^ r * (P.eval (16 * p.1 * p.2)) ^ 2
private theorem literal_rectangle_energy_lower {a b : Real}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ C : Real, 0 < C ∧ ∀ (r : Nat) (P : Polynomial Real),
      C * ∫ p, literalProductEnergy r P p ∂((volume.restrict (Set.Icc a b)).prod
          (volume.restrict (Set.Icc a b))) ≤
        ∫ p, literalProductEnergy r P p ∂(catalanBetaMeasure.prod catalanBetaMeasure) := by
  let f : Real → Real := fun x => (1 / beta (1 / 2 : Real) (3 / 2 : Real)) *
      x ^ ((1 / 2 : Real) - 1) * (1 - x) ^ ((3 / 2 : Real) - 1)
  have hcontinuous : ContinuousOn (betaPDFReal (1 / 2 : Real) (3 / 2 : Real))
      (Set.Icc a b) := by
    have hf : ContinuousOn f (Set.Icc a b) := by
      dsimp [f]
      have hx : ContinuousOn (fun x : Real => x) (Set.Icc a b) := continuous_id.continuousOn
      have hone_sub : ContinuousOn (fun x : Real => 1 - x) (Set.Icc a b) :=
        (continuous_const.sub continuous_id).continuousOn
      exact (continuousOn_const.mul (hx.rpow_const fun x hx =>
        Or.inl (ne_of_gt (ha.trans_le hx.1)))).mul
          (hone_sub.rpow_const fun x hx =>
            Or.inl (ne_of_gt (sub_pos.mpr (hx.2.trans_lt hb))))
    refine hf.congr ?_
    intro x hx
    rw [betaPDFReal, if_pos]
    exact ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  obtain ⟨c, hc, hbound⟩ := isCompact_Icc.exists_forall_le'
    (a := (0 : Real)) hcontinuous fun x hx =>
      betaPDFReal_pos (ha.trans_le hx.1) (hx.2.trans_lt hb) (by norm_num) (by norm_num)
  have hmeasure : ENNReal.ofReal c • volume.restrict (Set.Icc a b) ≤
      catalanBetaMeasure.restrict (Set.Icc a b) := by
    rw [catalanBetaMeasure, betaMeasure, restrict_withDensity measurableSet_Icc,
      ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact ENNReal.ofReal_le_ofReal (hbound x hx)
  refine ⟨c ^ 2, sq_pos_of_pos hc, fun r P => ?_⟩
  have hrestricted : catalanBetaMeasure.restrict (Set.Icc a b) ≤ catalanBetaMeasure :=
    Measure.restrict_le_self
  have hprod :
      (ENNReal.ofReal c • volume.restrict (Set.Icc a b)).prod
          (ENNReal.ofReal c • volume.restrict (Set.Icc a b)) ≤
        catalanBetaMeasure.prod catalanBetaMeasure :=
    (Measure.prod_mono hmeasure hmeasure).trans
      (Measure.prod_mono hrestricted hrestricted)
  have hscaled : ENNReal.ofReal c ^ 2 • ((volume.restrict (Set.Icc a b)).prod
      (volume.restrict (Set.Icc a b))) ≤ catalanBetaMeasure.prod catalanBetaMeasure := by
    simpa [pow_two, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] using hprod
  have hscalar : ∀ᵐ x ∂catalanBetaMeasure, x ∈ Set.Ioo (0 : Real) 1 := by
    rw [catalanBetaMeasure, betaMeasure]
    refine (ae_withDensity_iff (measurable_betaPDFReal (1 / 2) (3 / 2)).ennreal_ofReal).2 ?_
    filter_upwards with x hx
    contrapose! hx
    rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hx)]
    simp
  have hsupport : ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
      p.1 ∈ Set.Ioo (0 : Real) 1 ∧ p.2 ∈ Set.Ioo (0 : Real) 1 := by
    change ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
      p ∈ Set.Ioo (0 : Real) 1 ×ˢ Set.Ioo (0 : Real) 1
    rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
    filter_upwards [hscalar] with x hx
    filter_upwards [hscalar] with y hy
    exact ⟨hx, hy⟩
  have hnonneg : 0 ≤ᵐ[catalanBetaMeasure.prod catalanBetaMeasure] literalProductEnergy r P := by
    filter_upwards [hsupport] with p hp
    exact mul_nonneg (pow_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hp.1.1.le) hp.2.1.le) r) (sq_nonneg _)
  have hintegrable : Integrable (literalProductEnergy r P)
      (catalanBetaMeasure.prod catalanBetaMeasure) := by
    let f : BoundedContinuousFunction (Real × Real) Real :=
      clippedCatalanProductCoordinate ^ r *
      (P.eval₂ (algebraMap Real (BoundedContinuousFunction (Real × Real) Real))
        clippedCatalanProductCoordinate) ^ 2
    refine (f.integrable (μ := catalanBetaMeasure.prod catalanBetaMeasure)).congr ?_
    filter_upwards [hsupport] with p hp
    have hclip : clippedCatalanProductCoordinate p = (4 * p.1) * (4 * p.2) := by
      simp only [clippedCatalanProductCoordinate,
        BoundedContinuousFunction.coe_ofNormedAddCommGroup]
      change (4 * (Set.projIcc 0 1 zero_le_one p.1 : Real)) *
        (4 * (Set.projIcc 0 1 zero_le_one p.2 : Real)) = _
      rw [Set.projIcc_of_mem zero_le_one ⟨hp.1.1.le, hp.1.2.le⟩,
        Set.projIcc_of_mem zero_le_one ⟨hp.2.1.le, hp.2.2.le⟩]
    have heval (Q : Polynomial Real) :
        (Q.eval₂ (algebraMap Real (BoundedContinuousFunction (Real × Real) Real))
          clippedCatalanProductCoordinate) p = Q.eval (clippedCatalanProductCoordinate p) := by
      induction Q using Polynomial.induction_on' with
      | add Q R hQ hR => simp [hQ, hR]
      | monomial n x => simp
    simp only [f, BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.pow_apply, literalProductEnergy]
    rw [heval]
    rw [hclip]
    congr 2 <;> ring
  have h := integral_mono_measure hscaled hnonneg hintegrable
  simpa [MeasureTheory.integral_smul_measure, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hc.le] using h
private theorem literal_central_interval_energy_lower {δ : Real}
    (hδ0 : 0 < δ) (hδ8 : δ < 8) :
    ∃ C : Real, 0 < C ∧ ∀ (r : Nat) (P : Polynomial Real),
      C * δ ^ r * ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 ≤
        ∫ p, (16 * p.1 * p.2) ^ r * (P.eval (16 * p.1 * p.2)) ^ 2
          ∂(catalanBetaMeasure.prod catalanBetaMeasure) := by
  have hab : δ / 64 ≤ 1 - δ / 64 := by nlinarith
  obtain ⟨c, hc, hrectangle⟩ := literal_rectangle_energy_lower
    (a := δ / 64) (b := 1 - δ / 64)
    (by positivity) hab (by nlinarith)
  refine ⟨c * δ / 1024, by positivity, fun r P => ?_⟩
  let G : Real → Real := fun z => z ^ r * (P.eval z) ^ 2
  let F : Real × Real → Real := fun p =>
    (16 * p.1 * p.2) ^ r * (P.eval (16 * p.1 * p.2)) ^ 2
  have hδrange : δ ≤ 16 - δ := by nlinarith
  have hGcontinuous : Continuous G := by
    exact (continuous_id.pow r).mul ((P.continuous).pow 2)
  have hFcontinuous : Continuous F := by
    exact (((continuous_const.mul continuous_fst).mul continuous_snd).pow r).mul
      ((P.continuous.comp ((continuous_const.mul continuous_fst).mul continuous_snd)).pow 2)
  have hFint : Integrable F
      ((volume.restrict (Set.Icc (δ / 64) (1 - δ / 64))).prod
        (volume.restrict (Set.Icc (δ / 64) (1 - δ / 64)))) := by
    rw [Measure.prod_restrict]
    exact hFcontinuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hcentral_weighted :
      δ ^ r * ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 ≤
        ∫ z in Set.Icc δ (16 - δ), G z := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on
      ((continuous_const.mul ((P.continuous).pow 2)).continuousOn.integrableOn_Icc)
      (hGcontinuous.continuousOn.integrableOn_Icc) measurableSet_Icc ?_
    intro z hz
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hδ0.le hz.1 r) (sq_nonneg (P.eval z))
  have hweighted_nonneg : 0 ≤ ∫ z in Set.Icc δ (16 - δ), G z := by
    exact setIntegral_nonneg measurableSet_Icc fun z hz =>
      mul_nonneg (pow_nonneg (hδ0.le.trans hz.1) r) (sq_nonneg (P.eval z))
  have hinner (y : Real)
      (hy : y ∈ Set.Icc (1 - δ / 32) (1 - δ / 64)) :
      (1 / 16 : Real) * δ ^ r * ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 ≤
        ∫ x in Set.Icc (δ / 64) (1 - δ / 64), F (x, y) := by
    have hy0 : 0 < y := by nlinarith [hy.1]
    have hy1 : y ≤ 1 := by nlinarith [hy.2, hδ0]
    have hscale0 : 0 < 16 * y := mul_pos (by norm_num) hy0
    have hscale_ne : 16 * y ≠ 0 := ne_of_gt hscale0
    have hleft : δ / 64 ≤ δ / (16 * y) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : Real) < 64) hscale0).2
      nlinarith [mul_le_mul_of_nonneg_left hy1 hδ0.le]
    have hlr : δ / (16 * y) ≤ (16 - δ) / (16 * y) := by
      exact (div_le_div_iff_of_pos_right hscale0).2 hδrange
    have hright : (16 - δ) / (16 * y) ≤ 1 - δ / 64 := by
      have hq : 0 ≤ 1 - δ / 64 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hy.1 hq
      apply (div_le_iff₀ hscale0).2
      nlinarith [hmul, sq_nonneg δ]
    have hslice : IntervalIntegrable (fun x : Real => F (x, y)) volume
        (δ / 64) (1 - δ / 64) := by
      simpa [Function.comp_def] using
        (hFcontinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable
          (μ := volume) (δ / 64) (1 - δ / 64)
    have hsubinterval :
        (∫ x in δ / (16 * y)..(16 - δ) / (16 * y), F (x, y)) ≤
          ∫ x in δ / 64..1 - δ / 64, F (x, y) := by
      refine intervalIntegral.integral_mono_interval hleft hlr hright ?_ hslice
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 ≤ x := by nlinarith [hx.1, hδ0]
      exact mul_nonneg
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx0) hy0.le) r) (sq_nonneg _)
    have hchange :
        (∫ x in δ / (16 * y)..(16 - δ) / (16 * y), F (x, y)) =
          (16 * y)⁻¹ * ∫ z in δ..16 - δ, G z := by
      calc
        (∫ x in δ / (16 * y)..(16 - δ) / (16 * y), F (x, y)) =
            ∫ x in δ / (16 * y)..(16 - δ) / (16 * y), G ((16 * y) * x) := by
              apply intervalIntegral.integral_congr
              intro x _
              simp only [F, G]
              congr 2 <;> ring
        _ = (16 * y)⁻¹ * ∫ z in δ..16 - δ, G z := by
          have hleftscale : (16 * y) * (δ / (16 * y)) = δ := by
            field_simp
          have hrightscale : (16 * y) * ((16 - δ) / (16 * y)) = 16 - δ := by
            field_simp
          rw [intervalIntegral.integral_comp_mul_left G hscale_ne,
            hleftscale, hrightscale, smul_eq_mul]
    have hIcc_weighted :
        (∫ z in Set.Icc δ (16 - δ), G z) = ∫ z in δ..16 - δ, G z := by
      rw [intervalIntegral.integral_of_le hδrange, ← integral_Icc_eq_integral_Ioc]
    have hinv : (1 / 16 : Real) ≤ (16 * y)⁻¹ := by
      rw [inv_eq_one_div]
      exact (div_le_div_iff₀ (by norm_num : (0 : Real) < 16) hscale0).2
        (by nlinarith)
    have hscaled_weighted :
        (1 / 16 : Real) * (∫ z in Set.Icc δ (16 - δ), G z) ≤
          (16 * y)⁻¹ * ∫ z in δ..16 - δ, G z := by
      rw [← hIcc_weighted]
      exact mul_le_mul_of_nonneg_right hinv hweighted_nonneg
    calc
      (1 / 16 : Real) * δ ^ r *
            ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 =
          (1 / 16 : Real) *
            (δ ^ r * ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2) := by ring
      _ ≤ (1 / 16 : Real) * ∫ z in Set.Icc δ (16 - δ), G z :=
        mul_le_mul_of_nonneg_left hcentral_weighted (by norm_num)
      _ ≤ (16 * y)⁻¹ * ∫ z in δ..16 - δ, G z := hscaled_weighted
      _ = ∫ x in δ / (16 * y)..(16 - δ) / (16 * y), F (x, y) := hchange.symm
      _ ≤ ∫ x in δ / 64..1 - δ / 64, F (x, y) := hsubinterval
      _ = ∫ x in Set.Icc (δ / 64) (1 - δ / 64), F (x, y) := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hJsubset : Set.Icc (1 - δ / 32) (1 - δ / 64) ⊆
      Set.Icc (δ / 64) (1 - δ / 64) := by
    intro y hy
    exact ⟨by nlinarith [hy.1], hy.2⟩
  have houter : IntegrableOn
      (fun y => ∫ x in Set.Icc (δ / 64) (1 - δ / 64), F (x, y))
      (Set.Icc (δ / 64) (1 - δ / 64)) volume := by
    change Integrable
      (fun y => ∫ x, F (x, y) ∂volume.restrict
        (Set.Icc (δ / 64) (1 - δ / 64)))
      (volume.restrict (Set.Icc (δ / 64) (1 - δ / 64)))
    exact hFint.integral_prod_right
  have houter_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (δ / 64) (1 - δ / 64))]
        (fun y => ∫ x in Set.Icc (δ / 64) (1 - δ / 64), F (x, y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact setIntegral_nonneg measurableSet_Icc fun (x : Real) hx =>
      mul_nonneg (pow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (by nlinarith [hx.1, hδ0]))
          (by nlinarith [hy.1, hδ0])) r) (sq_nonneg _)
  have hJmono :
      (∫ y in Set.Icc (1 - δ / 32) (1 - δ / 64),
          (1 / 16 : Real) * δ ^ r *
            ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2) ≤
        ∫ y in Set.Icc (1 - δ / 32) (1 - δ / 64),
          ∫ x in Set.Icc (δ / 64) (1 - δ / 64), F (x, y) := by
    refine setIntegral_mono_on (continuousOn_const.integrableOn_Icc)
      (houter.mono_set hJsubset) measurableSet_Icc ?_
    exact hinner
  have hJtoRectangle :
      (∫ y in Set.Icc (1 - δ / 32) (1 - δ / 64),
          ∫ x in Set.Icc (δ / 64) (1 - δ / 64), F (x, y)) ≤
        ∫ y in Set.Icc (δ / 64) (1 - δ / 64),
          ∫ x in Set.Icc (δ / 64) (1 - δ / 64), F (x, y) :=
    setIntegral_mono_set houter houter_nonneg hJsubset.eventuallyLE
  have hJvolume :
      (∫ _y in Set.Icc (1 - δ / 32) (1 - δ / 64),
          (1 / 16 : Real) * δ ^ r *
            ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2) =
        δ / 1024 * δ ^ r *
          ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal]
    · ring
    · nlinarith
  have hgeometry :
      δ / 1024 * δ ^ r * ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 ≤
        ∫ p, F p
          ∂((volume.restrict (Set.Icc (δ / 64) (1 - δ / 64))).prod
            (volume.restrict (Set.Icc (δ / 64) (1 - δ / 64)))) := by
    rw [← hJvolume]
    refine hJmono.trans (hJtoRectangle.trans ?_)
    exact (integral_prod_symm F hFint).symm.le
  have hscaled_geometry := mul_le_mul_of_nonneg_left hgeometry hc.le
  have hactual : c *
        (∫ p, F p
          ∂((volume.restrict (Set.Icc (δ / 64) (1 - δ / 64))).prod
            (volume.restrict (Set.Icc (δ / 64) (1 - δ / 64))))) ≤
      ∫ p, (16 * p.1 * p.2) ^ r * (P.eval (16 * p.1 * p.2)) ^ 2
        ∂(catalanBetaMeasure.prod catalanBetaMeasure) := by
    simpa [F, literalProductEnergy] using hrectangle r P
  calc
    c * δ / 1024 * δ ^ r *
          ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 =
        c * (δ / 1024 * δ ^ r *
          ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2) := by ring
    _ ≤ c *
        (∫ p, F p
          ∂((volume.restrict (Set.Icc (δ / 64) (1 - δ / 64))).prod
            (volume.restrict (Set.Icc (δ / 64) (1 - δ / 64))))) := hscaled_geometry
    _ ≤ ∫ p, (16 * p.1 * p.2) ^ r * (P.eval (16 * p.1 * p.2)) ^ 2
          ∂(catalanBetaMeasure.prod catalanBetaMeasure) := hactual
private theorem chebyshevU_weighted_orthogonality (n m : Nat) :
    (∫ x in Set.Icc (-1 : Real) 1,
      (Polynomial.Chebyshev.U Real n).eval x *
        (Polynomial.Chebyshev.U Real m).eval x * Real.sqrt (1 - x ^ 2)) =
      if n = m then Real.pi / 2 else 0 := by
  let f : Real → Real := fun x =>
    (Polynomial.Chebyshev.U Real n).eval x *
      (Polynomial.Chebyshev.U Real m).eval x * (1 - x ^ 2)
  have hweighted :
      (∫ x in Set.Icc (-1 : Real) 1,
        (Polynomial.Chebyshev.U Real n).eval x *
          (Polynomial.Chebyshev.U Real m).eval x * Real.sqrt (1 - x ^ 2)) =
        ∫ x, f x ∂Polynomial.Chebyshev.measureT := by
    rw [Polynomial.Chebyshev.integral_measureT,
      intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
    refine (setIntegral_congr_fun measurableSet_Icc fun x hx => ?_).symm
    have hs : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    by_cases hz : Real.sqrt (1 - x ^ 2) = 0
    · simp [f, hz]
    · have hid :
          (1 - x ^ 2) * Real.sqrt ((1 - x ^ 2)⁻¹) = Real.sqrt (1 - x ^ 2) := by
        rw [Real.sqrt_inv]
        calc
          _ = (Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) *
              (Real.sqrt (1 - x ^ 2))⁻¹ := by rw [Real.mul_self_sqrt hs]
          _ = _ := by field_simp
      simpa only [f, mul_assoc] using congrArg
        (fun t : Real => (Polynomial.Chebyshev.U Real n).eval x *
          (Polynomial.Chebyshev.U Real m).eval x * t) hid
  rw [hweighted, Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  have hpoint (θ : Real) :
      f (Real.cos θ) =
        Real.sin ((n + 1 : Nat) * θ) * Real.sin ((m + 1 : Nat) * θ) := by
    dsimp [f]
    rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
    rw [pow_two]
    calc
      (Polynomial.Chebyshev.U Real n).eval (Real.cos θ) *
            (Polynomial.Chebyshev.U Real m).eval (Real.cos θ) *
            (Real.sin θ * Real.sin θ) =
          ((Polynomial.Chebyshev.U Real n).eval (Real.cos θ) * Real.sin θ) *
            ((Polynomial.Chebyshev.U Real m).eval (Real.cos θ) * Real.sin θ) := by ring
      _ = _ := by
        rw [Polynomial.Chebyshev.U_real_cos, Polynomial.Chebyshev.U_real_cos]
        norm_num
  rw [intervalIntegral.integral_congr (fun θ _ => hpoint θ)]
  have hcos_int (k : Int) (hk : k ≠ 0) :
      (∫ θ in (0 : Real)..Real.pi, Real.cos ((k : Real) * θ)) = 0 := by
    calc
      _ = ∫ θ in (0 : Real)..Real.pi,
          (Polynomial.Chebyshev.T Real k).eval (Real.cos θ) := by simp
      _ = ∫ x, (Polynomial.Chebyshev.T Real k).eval x
          ∂Polynomial.Chebyshev.measureT :=
        (Polynomial.Chebyshev.integral_measureT_eq_integral_cos
          (f := fun x => (Polynomial.Chebyshev.T Real k).eval x)).symm
      _ = 0 := Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero hk
  calc
    _ =
        (1 / 2 : Real) * ∫ θ in (0 : Real)..Real.pi,
          2 * (Real.sin ((n + 1 : Nat) * θ) * Real.sin ((m + 1 : Nat) * θ)) := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1
            funext θ
            ring
    _ = (1 / 2 : Real) * ∫ θ in (0 : Real)..Real.pi,
          (Real.cos ((((n + 1 : Nat) : Real) - (m + 1 : Nat)) * θ) -
            Real.cos ((((n + 1 : Nat) : Real) + (m + 1 : Nat)) * θ)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro θ _
          simpa only [mul_assoc, sub_mul, add_mul, mul_sub, mul_add, mul_comm] using
            Real.two_mul_sin_mul_sin (((n + 1 : Nat) : Real) * θ)
              (((m + 1 : Nat) : Real) * θ)
    _ = if n = m then Real.pi / 2 else 0 := by
      rw [intervalIntegral.integral_sub]
      · by_cases hnm : n = m
        · subst m
          have hz : (∫ θ in (0 : Real)..Real.pi,
              Real.cos ((((n + 1 : Nat) : Real) + (n + 1 : Nat)) * θ)) = 0 := by
            convert hcos_int (2 * (n + 1 : Nat)) (by omega) using 1 <;> norm_num <;> ring
          rw [hz]
          simp
          ring
        · have hdiff : ((n + 1 : Nat) : Real) - (m + 1 : Nat) ≠ 0 := by
            exact sub_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_succ_iff.mpr hnm)
          have hsum : ((n + 1 : Nat) : Real) + (m + 1 : Nat) ≠ 0 := by positivity
          have hdiffzero : (∫ θ in (0 : Real)..Real.pi,
              Real.cos ((((n + 1 : Nat) : Real) - (m + 1 : Nat)) * θ)) = 0 := by
            convert hcos_int ((n : Int) - m) (by omega) using 1 <;> norm_num <;> ring
          have hsumzero : (∫ θ in (0 : Real)..Real.pi,
              Real.cos ((((n + 1 : Nat) : Real) + (m + 1 : Nat)) * θ)) = 0 := by
            convert hcos_int ((n : Int) + m + 2) (by omega) using 1 <;> norm_num <;> ring
          rw [hdiffzero, hsumzero]
          simp [hnm]
      · exact Real.continuous_cos.comp (continuous_const.mul continuous_id) |>.intervalIntegrable _ _
      · exact Real.continuous_cos.comp (continuous_const.mul continuous_id) |>.intervalIntegrable _ _
private def centralChebyshevAffine (δ : Real) : Polynomial Real :=
  (8 - δ)⁻¹ • (Polynomial.X - Polynomial.C 8)
private def centralChebyshevPolynomial (δ : Real) (k : Nat) : Polynomial Real :=
  ((8 - δ) / 2) ^ k •
    (Polynomial.Chebyshev.U Real k).comp (centralChebyshevAffine δ)
private theorem centralChebyshev_weighted_orthogonality {δ : Real}
    (hδ0 : 0 < δ) (hδ8 : δ < 8) (k j : Nat) :
    (∫ z in Set.Icc δ (16 - δ),
      (centralChebyshevPolynomial δ k).eval z *
        (centralChebyshevPolynomial δ j).eval z *
          Real.sqrt (1 - ((z - 8) / (8 - δ)) ^ 2)) =
      if k = j then
        ((8 - δ) / 2) ^ (2 * k) * (8 - δ) * Real.pi / 2 else 0 := by
  let L : Real := 8 - δ
  have hL : 0 < L := by dsimp [L]; linarith
  let F : Real → Real := fun z =>
    (centralChebyshevPolynomial δ k).eval z *
      (centralChebyshevPolynomial δ j).eval z *
        Real.sqrt (1 - ((z - 8) / L) ^ 2)
  have heval (k : Nat) (z : Real) :
      (centralChebyshevPolynomial δ k).eval z =
        ((8 - δ) / 2) ^ k *
          (Polynomial.Chebyshev.U Real k).eval ((z - 8) / (8 - δ)) := by
    simp only [centralChebyshevPolynomial, Polynomial.eval_smul,
      Polynomial.eval_comp, smul_eq_mul]
    congr 2
    simp [centralChebyshevAffine, div_eq_mul_inv]
    ring
  have hchange :
      (∫ z in δ..16 - δ, F z) = L * ∫ x in (-1 : Real)..1, F (L * x + 8) := by
    have h := intervalIntegral.smul_integral_comp_mul_add F L (8 : Real)
      (a := (-1 : Real)) (b := 1)
    rw [smul_eq_mul] at h
    convert h.symm using 1 <;> dsimp [L] <;> ring
  have hpoint (x : Real) :
      F (L * x + 8) =
        (((8 - δ) / 2) ^ k * ((8 - δ) / 2) ^ j) *
          ((Polynomial.Chebyshev.U Real k).eval x *
            (Polynomial.Chebyshev.U Real j).eval x * Real.sqrt (1 - x ^ 2)) := by
    have hx : (L * x + 8 - 8) / (8 - δ) = x := by
      dsimp [L]
      field_simp [sub_ne_zero.mpr hδ8.ne']
      ring
    have hxL : (L * x + 8 - 8) / L = x := by
      rw [show L * x + 8 - 8 = L * x by ring]
      exact mul_div_cancel_left₀ x (ne_of_gt hL)
    dsimp only [F]
    rw [heval, heval, hx]
    ring
  have hortho :
      (∫ x in (-1 : Real)..1,
        (Polynomial.Chebyshev.U Real k).eval x *
          (Polynomial.Chebyshev.U Real j).eval x * Real.sqrt (1 - x ^ 2)) =
        if k = j then Real.pi / 2 else 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
    exact chebyshevU_weighted_orthogonality k j
  rw [show (∫ z in Set.Icc δ (16 - δ), F z) = ∫ z in δ..16 - δ, F z by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]]
  rw [hchange]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, hortho]
  by_cases hkj : k = j
  · subst j
    simp only [if_pos rfl]
    have hp : ((8 - δ) / 2) ^ k * ((8 - δ) / 2) ^ k =
        ((8 - δ) / 2) ^ (2 * k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp]
    dsimp [L]
    ring
  · simp [hkj]
private theorem central_polynomial_energy_lower {δ : Real}
    (hδ0 : 0 < δ) (hδ8 : δ < 8) (n : Nat) (a : Fin n → Real) :
    (∑ i : Fin n, a i ^ 2 *
      (((8 - δ) / 2) ^ (2 * i.1) * (8 - δ) * Real.pi / 2)) ≤
      ∫ z in Set.Icc δ (16 - δ),
        ((∑ i : Fin n, a i • centralChebyshevPolynomial δ i.1).eval z) ^ 2 := by
  let P : Polynomial Real := ∑ i : Fin n, a i • centralChebyshevPolynomial δ i.1
  let w : Real → Real := fun z => Real.sqrt (1 - ((z - 8) / (8 - δ)) ^ 2)
  have hδrange : δ ≤ 16 - δ := by linarith
  have hwcontinuous : Continuous w := by
    dsimp [w]
    fun_prop
  have horth (i j : Fin n) :
      (∫ z in Set.Icc δ (16 - δ),
        (centralChebyshevPolynomial δ i.1).eval z *
          (centralChebyshevPolynomial δ j.1).eval z * w z) =
        if i = j then
          ((8 - δ) / 2) ^ (2 * i.1) * (8 - δ) * Real.pi / 2 else 0 := by
    dsimp [w]
    rw [centralChebyshev_weighted_orthogonality hδ0 hδ8 i.1 j.1]
    by_cases hij : i = j
    · subst j
      simp
    · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      simp [hij, hval]
  have hexpand (z : Real) :
      (P.eval z) ^ 2 * w z =
        ∑ i : Fin n, ∑ j : Fin n,
          (a i * a j) *
            ((centralChebyshevPolynomial δ i.1).eval z *
              (centralChebyshevPolynomial δ j.1).eval z * w z) := by
    dsimp [P]
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_smul, smul_eq_mul, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hintegrable (i j : Fin n) : IntegrableOn
      (fun z => (a i * a j) *
        ((centralChebyshevPolynomial δ i.1).eval z *
          (centralChebyshevPolynomial δ j.1).eval z * w z))
      (Set.Icc δ (16 - δ)) volume := by
    exact (continuous_const.mul (((centralChebyshevPolynomial δ i.1).continuous.mul
      (centralChebyshevPolynomial δ j.1).continuous).mul hwcontinuous)).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hweighted :
      (∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 * w z) =
        ∑ i : Fin n, a i ^ 2 *
          (((8 - δ) / 2) ^ (2 * i.1) * (8 - δ) * Real.pi / 2) := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun z _ => hexpand z)]
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ fun j _ => hintegrable i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum _ (fun j _ => hintegrable i j)]
    simp_rw [integral_const_mul, horth]
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j _ hji
      have hij : i ≠ j := Ne.symm hji
      simp [hij]
    · simp
  have hweight_le :
      (∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 * w z) ≤
        ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 := by
    refine setIntegral_mono_on
      (((P.continuous.pow 2).mul hwcontinuous).continuousOn.integrableOn_Icc)
      ((P.continuous.pow 2).continuousOn.integrableOn_Icc) measurableSet_Icc ?_
    intro z hz
    have hL : 0 < 8 - δ := by linarith
    have ht : |(z - 8) / (8 - δ)| ≤ 1 := by
      rw [abs_le]
      constructor
      · apply (le_div_iff₀ hL).2
        nlinarith [hz.1]
      · apply (div_le_iff₀ hL).2
        nlinarith [hz.2]
    have hs : 0 ≤ 1 - ((z - 8) / (8 - δ)) ^ 2 := by
      rcases abs_le.mp ht with ⟨htl, htu⟩
      nlinarith [sq_nonneg (1 - (z - 8) / (8 - δ)),
        sq_nonneg (1 + (z - 8) / (8 - δ))]
    have hw0 : 0 ≤ w z := Real.sqrt_nonneg _
    have hw1 : w z ≤ 1 := by
      dsimp [w]
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg ((z - 8) / (8 - δ))]
    exact mul_le_of_le_one_right (sq_nonneg _) hw1
  rw [← hweighted]
  exact hweight_le
private theorem det_scalar_identity_add_posSemidef_lower {n : Nat}
    (K : Real) (hK : 0 ≤ K) (C : Matrix (Fin n) (Fin n) Real)
    (hC : C.PosSemidef) : K ^ n ≤ (K • (1 : Matrix (Fin n) (Fin n) Real) + C).det := by
  have hminor (s : Finset (Fin n)) :
      0 ≤ (C.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det :=
    (hC.submatrix _).det_nonneg
  have hcoeff (k : Nat) :
      0 ≤ (Matrix.det (1 + (Polynomial.X : Polynomial Real) • C.map Polynomial.C)).coeff k := by
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    exact Finset.sum_nonneg fun s hs => hminor s
  by_cases hK0 : K = 0
  · subst K
    by_cases hn : n = 0
    · subst n
      simp
    · simpa [zero_pow hn] using hC.det_nonneg
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    let p : Polynomial Real :=
      Matrix.det (1 + (Polynomial.X : Polynomial Real) • C.map Polynomial.C)
    have hfactor :
        (K • (1 : Matrix (Fin n) (Fin n) Real) + C).det =
          K ^ n * (1 + K⁻¹ • C).det := by
      have hmat : K • (1 : Matrix (Fin n) (Fin n) Real) + C =
          K • (1 + K⁻¹ • C) := by
        calc
          _ = K • (1 : Matrix (Fin n) (Fin n) Real) + K • (K⁻¹ • C) := by
            rw [smul_smul, mul_inv_cancel₀ hK0, one_smul]
          _ = _ := (smul_add K 1 (K⁻¹ • C)).symm
      rw [hmat, Matrix.det_smul, Fintype.card_fin]
    have hp0 : p.coeff 0 = 1 := by
      dsimp [p]
      rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
      simp
    have hzero_mem : 0 ∈ p.support := by
      rw [Polynomial.mem_support_iff, hp0]
      norm_num
    have hone : 1 ≤ p.eval K⁻¹ := by
      rw [Polynomial.eval_eq_sum]
      calc
        1 = p.coeff 0 * K⁻¹ ^ 0 := by simp [hp0]
        _ ≤ p.support.sum (fun e => p.coeff e * K⁻¹ ^ e) := by
          apply Finset.single_le_sum
            (f := fun e => p.coeff e * K⁻¹ ^ e) (s := p.support) (a := 0)
          · intro k hk
            exact mul_nonneg (hcoeff k) (pow_nonneg (inv_nonneg.2 hK) _)
          · exact hzero_mem
    have heval : p.eval K⁻¹ = (1 + K⁻¹ • C).det := by
      dsimp [p]
      rw [eval_det]
      congr 1
      ext i j
      simp
      ring
    rw [hfactor, ← heval]
    exact (le_mul_iff_one_le_right (pow_pos hKpos n)).2 hone
private def changedProductFunction (n : Nat) (δ : Real) (j : Fin n)
    (v : Nat → Real × Real →ᵇ Real) : Real × Real →ᵇ Real :=
  ∑ i : Fin n, (centralChebyshevPolynomial δ j.1).coeff i.1 • v i.1
private theorem normalized_changed_energy_lower {n r : Nat} {δ C : Real}
    (hδ0 : 0 < δ) (hδ8 : δ < 8) (hC : 0 < C)
    (hcentral : ∀ P : Polynomial Real,
      C * δ ^ r * ∫ z in Set.Icc δ (16 - δ), (P.eval z) ^ 2 ≤
        ∫ p, (16 * p.1 * p.2) ^ r * (P.eval (16 * p.1 * p.2)) ^ 2
          ∂(catalanBetaMeasure.prod catalanBetaMeasure))
    (v : Nat → Real × Real →ᵇ Real)
    (hv : ∀ i p, v i p = v 0 p * clippedCatalanProductCoordinate p ^ i)
    (hv0 : ∀ p, p.1 ∈ Set.Ioo (0 : Real) 1 ∧ p.2 ∈ Set.Ioo (0 : Real) 1 →
      (v 0 p) ^ 2 = (16 * p.1 * p.2) ^ r) (x : Fin n → Real) :
    C * δ ^ r * ∑ j : Fin n, x j ^ 2 ≤
      inner Real
        (∑ j : Fin n, x j •
          (Real.sqrt (((8 - δ) / 2) ^ (2 * j.1) * (8 - δ) * Real.pi / 2))⁻¹ •
            BoundedContinuousFunction.toLp 2
              (catalanBetaMeasure.prod catalanBetaMeasure) Real
              (changedProductFunction n δ j v))
        (∑ j : Fin n, x j •
          (Real.sqrt (((8 - δ) / 2) ^ (2 * j.1) * (8 - δ) * Real.pi / 2))⁻¹ •
            BoundedContinuousFunction.toLp 2
              (catalanBetaMeasure.prod catalanBetaMeasure) Real
              (changedProductFunction n δ j v)) := by
  let h : Fin n → Real := fun j =>
    ((8 - δ) / 2) ^ (2 * j.1) * (8 - δ) * Real.pi / 2
  let a : Fin n → Real := fun j => x j * (Real.sqrt (h j))⁻¹
  let Q : Polynomial Real := ∑ j : Fin n, a j • centralChebyshevPolynomial δ j.1
  let W : Real × Real →ᵇ Real := ∑ j : Fin n,
    x j • (Real.sqrt (h j))⁻¹ • changedProductFunction n δ j v
  have hAffineDegree : (centralChebyshevAffine δ).natDegree = 1 := by
    rw [centralChebyshevAffine, Polynomial.natDegree_smul_of_smul_regular,
      Polynomial.natDegree_X_sub_C]
    exact IsSMulRegular.of_ne_zero (inv_ne_zero (sub_ne_zero.mpr hδ8.ne'))
  have hAffineLeading : (centralChebyshevAffine δ).leadingCoeff = (8 - δ)⁻¹ := by
    rw [centralChebyshevAffine, Polynomial.leadingCoeff_smul_of_smul_regular,
      Polynomial.leadingCoeff_X_sub_C]
    · simp
    · exact IsSMulRegular.of_ne_zero (inv_ne_zero (sub_ne_zero.mpr hδ8.ne'))
  have hdegree (k : Nat) : (centralChebyshevPolynomial δ k).natDegree = k := by
    rw [centralChebyshevPolynomial, Polynomial.natDegree_smul_of_smul_regular]
    · rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
      · simp [Polynomial.Chebyshev.natDegree_U_natCast, hAffineDegree]
      · rw [Polynomial.Chebyshev.leadingCoeff_U_natCast, hAffineLeading]
        positivity
    · exact IsSMulRegular.of_ne_zero (by positivity)
  have hchanged (j : Fin n) (p : Real × Real) :
      changedProductFunction n δ j v p =
        v 0 p * (centralChebyshevPolynomial δ j.1).eval
          (clippedCatalanProductCoordinate p) := by
    change (BoundedContinuousFunction.evalCLM Real p)
        (∑ i : Fin n, (centralChebyshevPolynomial δ j.1).coeff i.1 • v i.1) = _
    rw [map_sum]
    simp only [map_smul, BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
        (centralChebyshevPolynomial δ j.1).coeff i * v i p) n,
      Polynomial.eval_eq_sum_range'
        (show (centralChebyshevPolynomial δ j.1).natDegree < n by
          rw [hdegree]
          exact j.2)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hv]
    ring
  have hh (j : Fin n) : 0 < h j := by
    dsimp [h]
    positivity
  have hdiag : ∑ j : Fin n, a j ^ 2 * h j = ∑ j : Fin n, x j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a]
    rw [mul_pow, inv_pow]
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hh j))]
    rw [Real.sq_sqrt (hh j).le]
  have hW (p : Real × Real) :
      W p = v 0 p * Q.eval (clippedCatalanProductCoordinate p) := by
    dsimp [W, Q, a]
    change (BoundedContinuousFunction.evalCLM Real p)
      (∑ j : Fin n, x j • (Real.sqrt (h j))⁻¹ •
        changedProductFunction n δ j v) = _
    rw [map_sum]
    simp only [map_smul, BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
    rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hchanged j p]
    simp only [Polynomial.eval_smul, smul_eq_mul]
    ring
  have hsum :
      (∑ j : Fin n, x j •
        (Real.sqrt (h j))⁻¹ •
          BoundedContinuousFunction.toLp 2
            (catalanBetaMeasure.prod catalanBetaMeasure) Real
            (changedProductFunction n δ j v)) =
        BoundedContinuousFunction.toLp 2
          (catalanBetaMeasure.prod catalanBetaMeasure) Real W := by
    dsimp [W]
    simp only [map_sum, map_smul, smul_smul]
  have hscalar : ∀ᵐ z ∂catalanBetaMeasure, z ∈ Set.Ioo (0 : Real) 1 := by
    rw [catalanBetaMeasure, betaMeasure]
    refine (ae_withDensity_iff (measurable_betaPDFReal (1 / 2) (3 / 2)).ennreal_ofReal).2 ?_
    filter_upwards with z hz
    contrapose! hz
    rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hz)]
    simp
  have hsupport : ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
      p.1 ∈ Set.Ioo (0 : Real) 1 ∧ p.2 ∈ Set.Ioo (0 : Real) 1 := by
    change ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
      p ∈ Set.Ioo (0 : Real) 1 ×ˢ Set.Ioo (0 : Real) 1
    rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
    filter_upwards [hscalar] with z hz
    filter_upwards [hscalar] with y hy
    exact ⟨hz, hy⟩
  have hinner : inner Real
      (BoundedContinuousFunction.toLp 2
        (catalanBetaMeasure.prod catalanBetaMeasure) Real W)
      (BoundedContinuousFunction.toLp 2
        (catalanBetaMeasure.prod catalanBetaMeasure) Real W) =
      ∫ p, (16 * p.1 * p.2) ^ r * (Q.eval (16 * p.1 * p.2)) ^ 2
        ∂(catalanBetaMeasure.prod catalanBetaMeasure) := by
    rw [BoundedContinuousFunction.inner_toLp]
    apply integral_congr_ae
    filter_upwards [hsupport] with p hp
    have hclip : clippedCatalanProductCoordinate p = (4 * p.1) * (4 * p.2) := by
      simp only [clippedCatalanProductCoordinate,
        BoundedContinuousFunction.coe_ofNormedAddCommGroup]
      change (4 * (Set.projIcc 0 1 zero_le_one p.1 : Real)) *
        (4 * (Set.projIcc 0 1 zero_le_one p.2 : Real)) = _
      rw [Set.projIcc_of_mem zero_le_one ⟨hp.1.1.le, hp.1.2.le⟩,
        Set.projIcc_of_mem zero_le_one ⟨hp.2.1.le, hp.2.2.le⟩]
    simp only [map_mul, conj_trivial]
    rw [hW, hclip]
    rw [show (v 0 p * Q.eval (4 * p.1 * (4 * p.2))) *
        (v 0 p * Q.eval (4 * p.1 * (4 * p.2))) =
        (v 0 p) ^ 2 * (Q.eval (4 * p.1 * (4 * p.2))) ^ 2 by ring,
      hv0 p hp]
    congr 2 <;> ring
  rw [show (∑ j : Fin n, x j ^ 2) = ∑ j : Fin n, a j ^ 2 * h j by
    exact hdiag.symm]
  rw [hsum, hinner]
  exact (mul_le_mul_of_nonneg_left
    (central_polynomial_energy_lower hδ0 hδ8 n a)
    (mul_nonneg hC.le (pow_nonneg hδ0.le r))).trans (hcentral Q)
private theorem catalan_square_hankel_det_lower {δ : Real} (hδ0 : 0 < δ) (hδ8 : δ < 8) :
    ∃ C : Real, 0 < C ∧ ∀ n : Nat,
      (C * δ) ^ n * ((8 - δ) * Real.pi / 2) ^ n *
          ((8 - δ) / 2) ^ (n * (n - 1)) ≤ catalanSquareHankelDet 1 n ∧
        (C * δ ^ 2) ^ n * ((8 - δ) * Real.pi / 2) ^ n *
          ((8 - δ) / 2) ^ (n * (n - 1)) ≤ catalanSquareHankelDet 2 n := by
  obtain ⟨C, hC, hcentral⟩ := literal_central_interval_energy_lower hδ0 hδ8
  refine ⟨C, hC, fun n => ?_⟩
  have clip_on_support (p : Real × Real) (hp : p.1 ∈ Set.Ioo (0 : Real) 1 ∧
      p.2 ∈ Set.Ioo (0 : Real) 1) :
      clippedCatalanProductCoordinate p = (4 * p.1) * (4 * p.2) := by
    simp only [clippedCatalanProductCoordinate, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    change (4 * (Set.projIcc 0 1 zero_le_one p.1 : Real)) *
      (4 * (Set.projIcc 0 1 zero_le_one p.2 : Real)) = _
    rw [Set.projIcc_of_mem zero_le_one ⟨hp.1.1.le, hp.1.2.le⟩,
      Set.projIcc_of_mem zero_le_one ⟨hp.2.1.le, hp.2.2.le⟩]
  have prove_shift (r : Nat) (v : Nat → Real × Real →ᵇ Real)
      (vLp : Nat → Lp Real 2 (catalanBetaMeasure.prod catalanBetaMeasure))
      (hvLp : ∀ i, vLp i = BoundedContinuousFunction.toLp 2
        (catalanBetaMeasure.prod catalanBetaMeasure) Real (v i))
      (hv : ∀ i p, v i p = v 0 p * clippedCatalanProductCoordinate p ^ i)
      (hv0 : ∀ p, p.1 ∈ Set.Ioo (0 : Real) 1 ∧ p.2 ∈ Set.Ioo (0 : Real) 1 →
        (v 0 p) ^ 2 = (16 * p.1 * p.2) ^ r)
      (hgram : catalanSquareHankelMatrix n r =
        Matrix.gram Real (fun i : Fin n => vLp i.1)) :
      (C * δ ^ r) ^ n * ((8 - δ) * Real.pi / 2) ^ n *
          ((8 - δ) / 2) ^ (n * (n - 1)) ≤ catalanSquareHankelDet r n := by
    have hAffineDegree : (centralChebyshevAffine δ).natDegree = 1 := by
      rw [centralChebyshevAffine, Polynomial.natDegree_smul_of_smul_regular,
        Polynomial.natDegree_X_sub_C]
      exact IsSMulRegular.of_ne_zero (inv_ne_zero (sub_ne_zero.mpr hδ8.ne'))
    have hAffineLeading : (centralChebyshevAffine δ).leadingCoeff = (8 - δ)⁻¹ := by
      rw [centralChebyshevAffine, Polynomial.leadingCoeff_smul_of_smul_regular,
        Polynomial.leadingCoeff_X_sub_C]
      · simp
      · exact IsSMulRegular.of_ne_zero (inv_ne_zero (sub_ne_zero.mpr hδ8.ne'))
    have hdegree (k : Nat) : (centralChebyshevPolynomial δ k).natDegree = k := by
      rw [centralChebyshevPolynomial, Polynomial.natDegree_smul_of_smul_regular]
      · rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
        · simp [Polynomial.Chebyshev.natDegree_U_natCast, hAffineDegree]
        · rw [Polynomial.Chebyshev.leadingCoeff_U_natCast, hAffineLeading]
          positivity
      · exact IsSMulRegular.of_ne_zero (by positivity)
    have hmonic (k : Nat) : (centralChebyshevPolynomial δ k).Monic := by
      rw [Polynomial.Monic, centralChebyshevPolynomial,
        Polynomial.leadingCoeff_smul_of_smul_regular _
          (IsSMulRegular.of_ne_zero (by positivity)), Polynomial.leadingCoeff_comp]
      · rw [Polynomial.Chebyshev.leadingCoeff_U_natCast,
          Polynomial.Chebyshev.natDegree_U_natCast, hAffineLeading]
        have hL : 8 - δ ≠ 0 := sub_ne_zero.mpr hδ8.ne'
        rw [div_pow, smul_eq_mul, inv_pow]
        field_simp
      · rw [hAffineDegree]
        norm_num
    have htoLp (j : Fin n) : BoundedContinuousFunction.toLp 2
        (catalanBetaMeasure.prod catalanBetaMeasure) Real (changedProductFunction n δ j v) =
        ∑ i : Fin n, (centralChebyshevPolynomial δ j.1).coeff i.1 •
          BoundedContinuousFunction.toLp 2
            (catalanBetaMeasure.prod catalanBetaMeasure) Real (v i.1) := by
      simp only [changedProductFunction, map_sum, map_smul]
    let h : Fin n → Real := fun j => ((8 - δ) / 2) ^ (2 * j.1) * (8 - δ) * Real.pi / 2
    let s : Fin n → Real := fun j => Real.sqrt (h j)
    let w : Fin n → Lp Real 2 (catalanBetaMeasure.prod catalanBetaMeasure) :=
      fun j => BoundedContinuousFunction.toLp 2
        (catalanBetaMeasure.prod catalanBetaMeasure) Real
        (changedProductFunction n δ j v)
    let u : Fin n → Lp Real 2 (catalanBetaMeasure.prod catalanBetaMeasure) := fun j => (s j)⁻¹ • w j
    let K : Real := C * δ ^ r
    let G : Matrix (Fin n) (Fin n) Real := Matrix.gram Real u
    have hh (j : Fin n) : 0 < h j := by dsimp [h]; positivity
    have hs (j : Fin n) : 0 < s j := Real.sqrt_pos.2 (hh j)
    have henergy (x : Fin n → Real) : K * ∑ j : Fin n, x j ^ 2 ≤
        inner Real (∑ j : Fin n, x j • u j) (∑ j : Fin n, x j • u j) := by
      exact normalized_changed_energy_lower hδ0 hδ8 hC (hcentral r) v hv hv0 x
    have hpsd : (G - K • (1 : Matrix (Fin n) (Fin n) Real)).PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        ((Matrix.isHermitian_gram Real u).sub
          ((Matrix.PosSemidef.one.smul (mul_nonneg hC.le (pow_nonneg hδ0.le r))).isHermitian)) ?_
      intro x
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.star_dotProduct_gram_mulVec]
      have hscalar : dotProduct (star x)
          ((K • (1 : Matrix (Fin n) (Fin n) Real)).mulVec x) =
          K * ∑ j : Fin n, x j ^ 2 := by
        simp [Matrix.mulVec, dotProduct, pow_two, Matrix.one_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hscalar]
      exact sub_nonneg.mpr (henergy x)
    have hdetG : K ^ n ≤ G.det := by
      have hd := det_scalar_identity_add_posSemidef_lower K
        (mul_nonneg hC.le (pow_nonneg hδ0.le r))
        (G - K • (1 : Matrix (Fin n) (Fin n) Real)) hpsd
      rwa [show K • (1 : Matrix (Fin n) (Fin n) Real) +
          (G - K • (1 : Matrix (Fin n) (Fin n) Real)) = G by abel] at hd
    have hrecover (j : Fin n) : w j = s j • u j := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hs j)), one_smul]
    have hGram : Matrix.gram Real w = Matrix.diagonal s * G * Matrix.diagonal s := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.gram_apply]
      rw [hrecover i, hrecover j]
      simp [G, Matrix.gram_apply, inner_smul_left, inner_smul_right]
      ring
    have hchange : (Matrix.gram Real w).det = catalanSquareHankelDet r n := by
      change (Matrix.gram Real (fun j : Fin n =>
        BoundedContinuousFunction.toLp 2
          (catalanBetaMeasure.prod catalanBetaMeasure) Real
          (changedProductFunction n δ j v))).det = _
      simp_rw [htoLp]
      simp_rw [← hvLp]
      rw [det_gram_monic_polynomial_change n (fun i : Fin n => vLp i.1)
        (fun j : Fin n => centralChebyshevPolynomial δ j.1)
        (fun j => hdegree j.1) (fun j => hmonic j.1), ← hgram]
      rfl
    have hprod : (∏ j : Fin n, s j) ^ 2 = ((8 - δ) * Real.pi / 2) ^ n *
        ((8 - δ) / 2) ^ (n * (n - 1)) := by
      rw [← Finset.prod_pow]
      simp_rw [show ∀ j : Fin n, s j ^ 2 = h j from fun j => Real.sq_sqrt (hh j).le]
      dsimp [h]
      simp_rw [show ∀ j : Fin n,
          ((8 - δ) / 2) ^ (2 * j.1) * (8 - δ) * Real.pi / 2 =
            ((8 - δ) * Real.pi / 2) * ((8 - δ) / 2) ^ (2 * j.1) by
        intro j
        ring]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
      congr 2
      rw [Fin.sum_univ_eq_sum_range]
      simpa [Finset.mul_sum, mul_comm] using Finset.sum_range_id_mul_two n
    rw [← hchange, hGram, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal]
    calc
      K ^ n * ((8 - δ) * Real.pi / 2) ^ n *
          ((8 - δ) / 2) ^ (n * (n - 1)) =
          (∏ j : Fin n, s j) ^ 2 * K ^ n := by rw [hprod]; ring
      _ ≤ (∏ j : Fin n, s j) ^ 2 * G.det :=
        mul_le_mul_of_nonneg_left hdetG (sq_nonneg _)
      _ = (∏ j : Fin n, s j) * G.det * ∏ j : Fin n, s j := by ring
  constructor
  · simpa using prove_shift 1 productShiftOneGramVector productShiftOneLpVector
      (fun _ => rfl) (by intro i p; simp [productShiftOneGramVector, pow_succ'])
      (by
        intro p hp
        simp only [productShiftOneGramVector,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup, pow_zero, mul_one]
        have hclip := clip_on_support p hp
        have hz : 0 ≤ clippedCatalanProductCoordinate p := by
          rw [hclip]
          exact mul_nonneg (mul_nonneg (by norm_num) hp.1.1.le)
            (mul_nonneg (by norm_num) hp.2.1.le)
        rw [Real.sq_sqrt hz, hclip]
        ring)
      (catalanSquareHankelMatrix_eq_product_gram_one n)
  · simpa using prove_shift 2 productShiftTwoGramVector productShiftTwoLpVector
      (fun _ => rfl) (by intro i p; simp [productShiftTwoGramVector, pow_succ', pow_add])
      (by
        intro p hp
        simp [productShiftTwoGramVector, clip_on_support p hp]
        ring)
      (catalanSquareHankelMatrix_eq_product_gram_two n)
theorem catalan_square_hankel_log_limits :
    Tendsto (fun n : Nat => Real.log (catalanSquareHankelDet 1 n) / (n : Real) ^ 2) atTop (nhds (2 * Real.log 2)) ∧
      Tendsto (fun n : Nat => Real.log (catalanSquareHankelDet 2 n) / (n : Real) ^ 2) atTop (nhds (2 * Real.log 2)) := by
  have hlog4 : Real.log (4 : Real) = 2 * Real.log 2 := by rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have htri (n : Nat) : (16 : Real) ^ (n * (n - 1) / 2) = 4 ^ (n * (n - 1)) := by
    rw [show (16 : Real) = 4 ^ 2 by norm_num, ← pow_mul, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)]
  have prove_shift (r : Nat) (A : Real) (hA : 0 < A)
      (hpos : ∀ n, 0 < catalanSquareHankelDet r n)
      (hupp : ∀ n, catalanSquareHankelDet r n ≤ A ^ n * 16 ^ (n * (n - 1) / 2))
      (hlow : ∀ δ : Real, 0 < δ → δ < 8 → ∃ C : Real, 0 < C ∧ ∀ n,
        (C * δ ^ r) ^ n * ((8 - δ) * Real.pi / 2) ^ n *
          ((8 - δ) / 2) ^ (n * (n - 1)) ≤ catalanSquareHankelDet r n) :
      Tendsto (fun n : Nat => Real.log (catalanSquareHankelDet r n) / (n : Real) ^ 2) atTop (nhds (Real.log 4)) := by
    have rate {B q : Real} (hB : 0 < B) (hq : 0 < q) :
        Tendsto (fun n : Nat =>
          Real.log (B ^ n * q ^ (n * (n - 1))) / (n : Real) ^ 2)
          atTop (nhds (Real.log q)) := by
      have hi : Tendsto (fun n : Nat => ((n : Real))⁻¹) atTop (nhds 0) := tendsto_inv_atTop_nhds_zero_nat
      have ht : Tendsto (fun n : Nat =>
          Real.log B * (n : Real)⁻¹ + (1 - (n : Real)⁻¹) * Real.log q)
          atTop (nhds (Real.log q)) := by
        convert (hi.const_mul (Real.log B)).add ((hi.const_sub 1).mul_const (Real.log q)) using 1 <;> simp
      refine ht.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
      change Real.log B * (n : Real)⁻¹ + (1 - (n : Real)⁻¹) * Real.log q =
        Real.log (B ^ n * q ^ (n * (n - 1))) / (n : Real) ^ 2
      rw [Real.log_mul (pow_ne_zero _ hB.ne') (pow_ne_zero _ hq.ne'), Real.log_pow, Real.log_pow]
      norm_cast at hn ⊢
      push_cast [Nat.cast_sub hn]
      field_simp
    rw [tendsto_order]
    constructor
    · intro a ha
      let t := (a + Real.log 4) / 2
      let q := Real.exp t
      let δ := 8 - 2 * q
      have hq0 : 0 < q := Real.exp_pos _
      have hq4 : q < 4 := by
        rw [← Real.exp_log (by norm_num : (0 : Real) < 4)]
        exact Real.exp_lt_exp.mpr (by dsimp [t]; linarith)
      have hδ0 : 0 < δ := by dsimp [δ]; linarith
      have hδ8 : δ < 8 := by dsimp [δ]; linarith
      obtain ⟨C, hC, hlowC⟩ := hlow δ hδ0 hδ8
      let B := (C * δ ^ r) * ((8 - δ) * Real.pi / 2)
      have hB : 0 < B := by dsimp [B]; positivity
      have hrate := rate hB hq0
      have haq : a < Real.log q := by rw [Real.log_exp]; dsimp [t]; linarith
      filter_upwards [hrate.eventually (Ioi_mem_nhds haq), eventually_gt_atTop 0] with n hn hn0
      have hqeq : (8 - δ) / 2 = q := by dsimp [δ]; ring
      have hbd : B ^ n * q ^ (n * (n - 1)) ≤ catalanSquareHankelDet r n := by simpa [B, hqeq, mul_pow, mul_assoc] using hlowC n
      exact hn.trans_le ((div_le_div_iff_of_pos_right (by positivity : (0 : Real) < (n : Real) ^ 2)).2
        (Real.log_le_log (mul_pos (pow_pos hB _) (pow_pos hq0 _)) hbd))
    · intro b hb
      have hrate := rate hA (by norm_num : (0 : Real) < 4)
      filter_upwards [hrate.eventually (Iio_mem_nhds hb), eventually_gt_atTop 0] with n hn hn0
      have hud : catalanSquareHankelDet r n ≤ A ^ n * 4 ^ (n * (n - 1)) := by
        simpa [htri] using hupp n
      exact ((div_le_div_iff_of_pos_right (by positivity : (0 : Real) < (n : Real) ^ 2)).2
        (Real.log_le_log (hpos n) hud)).trans_lt hn
  rw [← hlog4]
  constructor
  · exact prove_shift 1 4 (by norm_num) (fun n => (catalan_square_hankel_det_positive n).1)
      (fun n => (catalan_square_hankel_det_upper n).1) (fun δ h0 h8 => by
        obtain ⟨C, hC, h⟩ := catalan_square_hankel_det_lower h0 h8
        exact ⟨C, hC, fun n => by simpa [pow_one] using (h n).1⟩)
  · exact prove_shift 2 16 (by norm_num) (fun n => (catalan_square_hankel_det_positive n).2)
      (fun n => (catalan_square_hankel_det_upper n).2) (fun δ h0 h8 => by
        obtain ⟨C, hC, h⟩ := catalan_square_hankel_det_lower h0 h8
        exact ⟨C, hC, fun n => (h n).2⟩)
end D5.S3.Constants.Moments.CatalanSquareHankelLimits
