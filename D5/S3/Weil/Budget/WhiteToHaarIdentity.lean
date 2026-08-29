/- GID: D5/S3/Weil/Budget/WhiteToHaarIdentity
   generality: I
   mirror-B: D5/B/S3/Weil/Budget/WhiteToHaarIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Resolvent-weighted white spectrum becomes Haar spectrum under Cayley transport. -/

import D5.S3.Weil.Budget.FullCirclePrimalAttainment
import D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/- Library-search audit trail (2026-08-29):
   * D5 searches for white-to-Haar transport, resolvent compactification, and a
     Circle-valued Cayley map found no exact theorem or compactification primitive.
   * The canonical `cayleyCharacter` and `normalizedCircleHaar` declarations are
     imported and reused instead of redeclared.
   * Pinned Mathlib has no Cauchy-to-Haar transport theorem. The local bridge uses
     `map_withDensity_abs_det_fderiv_eq_addHaar`, `AddCircle.measurePreserving_mk`,
     and `MeasurableEmbedding.comap_map`.
   * Body-shape searches for `Measure.map` of a resolvent `withDensity` through a
     Circle-valued Cayley map found no D5 declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace D5.S3.Weil.Budget.WhiteToHaarIdentity

open D5.S3.Weil.Budget.FullCirclePrimalAttainment
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The source's normalized Lebesgue spectrum `dxi / (2 * pi)`. -/
noncomputable def normalizedLebesgueSpectrum : Measure Real :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume

/-- The canonical all-pass Cayley character, regarded as a point of the unit circle. -/
noncomputable def cayleyCircle (a : Real) (ha : a ≠ 0) (xi : Real) : Circle :=
  Circle.ofConjDivSelf ((xi : Complex) - Complex.I * a) (by
    intro denominatorZero
    have imaginaryZero := congrArg Complex.im denominatorZero
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul,
      zero_sub, Complex.zero_im] at imaginaryZero
    apply ha
    linarith)

@[simp]
private theorem cayleyCircle_coe (a : Real) (ha : a ≠ 0) (xi : Real) :
    ((cayleyCircle a ha xi : Circle) : Complex) = cayleyCharacter a xi := by
  simp only [cayleyCircle, Circle.ofConjDivSelf, cayleyCharacter]
  congr 1
  apply Complex.ext <;> simp

/-- Resolvent compactification is the Cayley pushforward of the source measure
weighted by `(xi^2 + a^2)^{-1}`. -/
noncomputable def resolventCompactification
    (a : Real) (ha : a ≠ 0) (nu : Measure Real) : Measure Circle :=
  Measure.map (cayleyCircle a ha)
    (nu.withDensity fun xi => ENNReal.ofReal ((xi ^ 2 + a ^ 2)⁻¹))

private theorem cayleyCharacter_re (a xi : Real) :
    (cayleyCharacter a xi).re = (xi ^ 2 - a ^ 2) / (xi ^ 2 + a ^ 2) := by
  rw [cayleyCharacter, Complex.div_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, mul_zero, Complex.I_im, one_mul, Complex.sub_re,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, Complex.sub_im, Complex.normSq_apply]
  ring

private theorem cayleyCharacter_im (a xi : Real) :
    (cayleyCharacter a xi).im = (2 * a * xi) / (xi ^ 2 + a ^ 2) := by
  rw [cayleyCharacter, Complex.div_im]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, mul_zero, Complex.I_im, one_mul, Complex.sub_re,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, Complex.sub_im, Complex.normSq_apply]
  ring

private theorem cayleyCircle_eq_exp_angle
    (a : Real) (ha : 0 < a) (xi : Real) :
    cayleyCircle a ha.ne' xi =
      Circle.exp (Real.pi - 2 * Real.arctan (xi / a)) := by
  apply Subtype.ext
  rw [cayleyCircle_coe, Circle.coe_exp, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · rw [cayleyCharacter_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, Real.cos_pi_sub, Real.cos_two_mul,
      Real.cos_sq_arctan]
    field_simp
    ring
  · rw [cayleyCharacter_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, Real.sin_pi_sub,
      Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    let q : Real := 1 + (xi / a) ^ 2
    have qNonnegative : 0 <= q := by positivity
    have squareRootPositive : 0 < Real.sqrt q := by
      apply Real.sqrt_pos.2
      dsimp [q]
      positivity
    simp only [zero_add, add_zero]
    change 2 * a * xi / (xi ^ 2 + a ^ 2) =
      2 * (xi / a / Real.sqrt q) * (1 / Real.sqrt q)
    rw [show 2 * (xi / a / Real.sqrt q) * (1 / Real.sqrt q) =
        2 * (xi / a) / (Real.sqrt q) ^ 2 by
      field_simp [squareRootPositive.ne']]
    rw [Real.sq_sqrt qNonnegative]
    dsimp [q]
    field_simp [ha.ne']
    ring

private theorem angleMap_hasDerivAt (a : Real) (ha : 0 < a) (xi : Real) :
    HasDerivAt (fun x : Real => Real.pi - 2 * Real.arctan (x / a))
      (-(2 * a / (xi ^ 2 + a ^ 2))) xi := by
  have quotientDerivative : HasDerivAt (fun x : Real => x / a) (1 / a) xi :=
    (hasDerivAt_id xi).div_const a
  have arctanDerivative :=
    (Real.hasDerivAt_arctan (xi / a)).comp xi quotientDerivative
  convert (arctanDerivative.const_mul 2).const_sub Real.pi using 1 <;> try rfl
  field_simp [ha.ne']
  ring

private theorem angleMap_image (a : Real) (ha : 0 < a) :
    (fun xi : Real => Real.pi - 2 * Real.arctan (xi / a)) '' Set.univ =
      Set.Ioo 0 (2 * Real.pi) := by
  ext theta
  constructor
  · rintro ⟨xi, -, rfl⟩
    rcases Real.arctan_mem_Ioo (xi / a) with ⟨lower, upper⟩
    constructor <;> dsimp <;> linarith [Real.pi_pos]
  · intro thetaBounds
    rcases thetaBounds with ⟨thetaPositive, thetaUpper⟩
    have targetBounds :
        (Real.pi - theta) / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    rw [← Real.range_arctan] at targetBounds
    obtain ⟨z, hz⟩ := targetBounds
    refine ⟨z * a, Set.mem_univ _, ?_⟩
    change Real.pi - 2 * Real.arctan (z * a / a) = theta
    rw [mul_div_cancel_right₀ z ha.ne']
    linarith

private theorem angleMap_pushforward (a : Real) (ha : 0 < a) :
    Measure.map (fun xi : Real => Real.pi - 2 * Real.arctan (xi / a))
        (volume.withDensity fun xi => ENNReal.ofReal (2 * a / (xi ^ 2 + a ^ 2))) =
      volume.restrict (Set.Ioo 0 (2 * Real.pi)) := by
  let derivative : Real → Real →L[Real] Real := fun xi =>
    ContinuousLinearMap.toSpanSingleton Real (-(2 * a / (xi ^ 2 + a ^ 2)))
  have derivativeAt (xi : Real) :
      HasFDerivAt (fun x : Real => Real.pi - 2 * Real.arctan (x / a))
        (derivative xi) xi := by
    exact (angleMap_hasDerivAt a ha xi).hasFDerivAt
  have injective : Function.Injective
      (fun xi : Real => Real.pi - 2 * Real.arctan (xi / a)) := by
    intro x y hxy
    have harctan : Real.arctan (x / a) = Real.arctan (y / a) := by linarith
    have hdiv : x / a = y / a := Real.arctan_injective harctan
    exact (div_left_inj' ha.ne').mp hdiv
  have jacobian := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := volume) (s := Set.univ)
    (f := fun xi : Real => Real.pi - 2 * Real.arctan (xi / a))
    (f' := derivative) MeasurableSet.univ.nullMeasurableSet
    (fun xi _ => (derivativeAt xi).hasFDerivWithinAt) injective.injOn
  rw [Measure.restrict_univ, angleMap_image a ha] at jacobian
  convert jacobian using 1
  congr 2
  funext xi
  simp only [derivative, ContinuousLinearMap.det_toSpanSingleton]
  rw [abs_of_nonpos]
  · simp only [neg_neg]
  · exact neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num) ha.le) (by positivity))

private theorem jacobianDensity_cayley_pushforward (a : Real) (ha : 0 < a) :
    Measure.map (cayleyCircle a ha.ne')
        (volume.withDensity fun xi => ENNReal.ofReal (2 * a / (xi ^ 2 + a ^ 2))) =
      ENNReal.ofReal (2 * Real.pi) •
        ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let angleMap : Real → Real := fun xi => Real.pi - 2 * Real.arctan (xi / a)
  let angleToCircle : Real → Circle := fun theta =>
    AddCircle.homeomorphCircle' (theta : AddCircle (2 * Real.pi))
  have angleMapMeasurable : Measurable angleMap := by
    fun_prop
  have angleToCircleMeasurable : Measurable angleToCircle := by
    exact AddCircle.homeomorphCircle'.continuous.measurable.comp AddCircle.measurable_mk'
  have cayleyFactorization : cayleyCircle a ha.ne' = angleToCircle ∘ angleMap := by
    funext xi
    simp only [Function.comp_apply, angleToCircle, angleMap,
      AddCircle.homeomorphCircle'_apply_mk]
    exact cayleyCircle_eq_exp_angle a ha xi
  rw [cayleyFactorization, ← Measure.map_map angleToCircleMeasurable angleMapMeasurable,
    angleMap_pushforward a ha]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  change Measure.map (AddCircle.homeomorphCircle' ∘
      ((↑) : Real → AddCircle (2 * Real.pi)))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) = _
  rw [← Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable
    AddCircle.measurable_mk']
  have quotientPushforward := (AddCircle.measurePreserving_mk (2 * Real.pi) 0).map_eq
  simp only [zero_add] at quotientPushforward
  rw [quotientPushforward]
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.map_smul]
  rfl

private theorem withDensity_mono_measure
    {mu nu : Measure Real} (h : mu ≤ nu) (density : Real → ENNReal) :
    mu.withDensity density ≤ nu.withDensity density := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [MeasureTheory.withDensity_apply _ hs, MeasureTheory.withDensity_apply _ hs]
  exact MeasureTheory.lintegral_mono' (Measure.restrict_mono le_rfl h) le_rfl

private theorem cayleyCircle_measurableEmbedding (a : Real) (ha : 0 < a) :
    MeasurableEmbedding (cayleyCircle a ha.ne') := by
  have continuousCayley : Continuous (cayleyCircle a ha.ne') := by
    have factorization : cayleyCircle a ha.ne' = fun xi =>
        Circle.exp (Real.pi - 2 * Real.arctan (xi / a)) := by
      funext xi
      exact cayleyCircle_eq_exp_angle a ha xi
    rw [factorization]
    fun_prop
  have injectiveCayley : Function.Injective (cayleyCircle a ha.ne') := by
    intro x y hxy
    rw [cayleyCircle_eq_exp_angle a ha x, cayleyCircle_eq_exp_angle a ha y] at hxy
    have xAngle : Real.pi - 2 * Real.arctan (x / a) ∈ Set.Ico 0 (2 * Real.pi) := by
      rcases Real.arctan_mem_Ioo (x / a) with ⟨lower, upper⟩
      constructor <;> linarith
    have yAngle : Real.pi - 2 * Real.arctan (y / a) ∈ Set.Ico 0 (2 * Real.pi) := by
      rcases Real.arctan_mem_Ioo (y / a) with ⟨lower, upper⟩
      constructor <;> linarith
    have angleEquality := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
      (by linarith) xAngle yAngle hxy
    have arctanEquality : Real.arctan (x / a) = Real.arctan (y / a) := by linarith
    have divisionEquality : x / a = y / a := Real.arctan_injective arctanEquality
    exact (div_left_inj' ha.ne').mp divisionEquality
  exact continuousCayley.measurableEmbedding injectiveCayley

private theorem resolventCompactification_order_iff
    (a : Real) (ha : 0 < a) (mu nu : Measure Real) :
    mu ≤ nu ↔
      resolventCompactification a ha.ne' mu ≤
        resolventCompactification a ha.ne' nu := by
  let density : Real → ENNReal := fun xi => ENNReal.ofReal ((xi ^ 2 + a ^ 2)⁻¹)
  have densityMeasurable : Measurable density := by
    fun_prop
  have densityNonzero (xi : Real) : density xi ≠ 0 := by
    simp only [density]
    positivity
  have densityFinite (xi : Real) : density xi ≠ ⊤ := ENNReal.ofReal_ne_top
  have cayleyEmbedding := cayleyCircle_measurableEmbedding a ha
  constructor
  · intro h
    apply Measure.map_mono (withDensity_mono_measure h density) cayleyEmbedding.measurable
  · intro h
    have weightedOrder : mu.withDensity density ≤ nu.withDensity density := by
      rw [← cayleyEmbedding.comap_map (mu.withDensity density),
        ← cayleyEmbedding.comap_map (nu.withDensity density)]
      refine Measure.le_iff.2 fun s _ => ?_
      rw [cayleyEmbedding.comap_apply, cayleyEmbedding.comap_apply]
      exact h _
    have recoveredOrder := withDensity_mono_measure weightedOrder density⁻¹
    have recoverMu : (mu.withDensity density).withDensity density⁻¹ = mu := by
      exact MeasureTheory.withDensity_inv_same densityMeasurable
        (Filter.Eventually.of_forall densityNonzero)
        (Filter.Eventually.of_forall densityFinite)
    have recoverNu : (nu.withDensity density).withDensity density⁻¹ = nu := by
      exact MeasureTheory.withDensity_inv_same densityMeasurable
        (Filter.Eventually.of_forall densityNonzero)
        (Filter.Eventually.of_forall densityFinite)
    simpa only [recoverMu, recoverNu] using recoveredOrder

private theorem normalizedLebesgueSpectrum_compactification
    (a : Real) (ha : 0 < a) :
    resolventCompactification a ha.ne' normalizedLebesgueSpectrum =
      ENNReal.ofReal (1 / (2 * a)) •
        ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) := by
  let whiteScale : ENNReal := ENNReal.ofReal (1 / (2 * Real.pi))
  let resolventScale : ENNReal := ENNReal.ofReal (1 / (2 * a))
  let resolventDensity : Real → ENNReal := fun xi =>
    ENNReal.ofReal ((xi ^ 2 + a ^ 2)⁻¹)
  let jacobianDensity : Real → ENNReal := fun xi =>
    ENNReal.ofReal (2 * a / (xi ^ 2 + a ^ 2))
  have resolventDensityMeasurable : Measurable resolventDensity := by
    fun_prop
  have densityScaling : resolventDensity = resolventScale • jacobianDensity := by
    funext xi
    simp only [resolventDensity, resolventScale, jacobianDensity, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / (2 * a) : Real))]
    congr 1
    field_simp [ha.ne']
  rw [resolventCompactification, normalizedLebesgueSpectrum]
  change Measure.map (cayleyCircle a ha.ne')
    ((whiteScale • volume).withDensity resolventDensity) = _
  rw [MeasureTheory.withDensity_smul_measure, densityScaling,
    MeasureTheory.withDensity_smul resolventScale (by fun_prop), Measure.map_smul,
    Measure.map_smul, jacobianDensity_cayley_pushforward a ha]
  rw [smul_smul, smul_smul]
  congr 1
  simp only [whiteScale, resolventScale]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / (2 * Real.pi) : Real))]
  rw [← ENNReal.ofReal_mul
    (by positivity : 0 ≤ (1 / (2 * Real.pi) * (1 / (2 * a)) : Real))]
  congr 1
  field_simp [ha.ne', Real.pi_ne_zero]

private theorem resolventCompactification_smul
    (a : Real) (ha : a ≠ 0) (coefficient : ENNReal) (nu : Measure Real) :
    resolventCompactification a ha (coefficient • nu) =
      coefficient • resolventCompactification a ha nu := by
  simp only [resolventCompactification, MeasureTheory.withDensity_smul_measure,
    Measure.map_smul]

/-- Resolvent-weighted Cayley compactification sends normalized white spectrum to normalized
circle Haar spectrum, preserves arbitrary white intensities with the exact scale factor, reflects
the corresponding measure floor, and becomes scale-free at `a = 1 / 2`. -/
theorem white_to_haar_identity
    (a : Real) (ha : 0 < a) (lambda : ENNReal) (nu : Measure Real) :
    resolventCompactification a ha.ne' normalizedLebesgueSpectrum =
        ENNReal.ofReal (1 / (2 * a)) •
          ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ∧
    resolventCompactification a ha.ne' (lambda • normalizedLebesgueSpectrum) =
        (lambda * ENNReal.ofReal (1 / (2 * a))) •
          ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ∧
    ((lambda • normalizedLebesgueSpectrum ≤ nu) ↔
      (lambda * ENNReal.ofReal (1 / (2 * a))) •
          ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) ≤
        resolventCompactification a ha.ne' nu) ∧
    resolventCompactification (1 / 2 : Real) (by norm_num)
        (lambda • normalizedLebesgueSpectrum) =
      lambda • ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) := by
  have baseIdentity := normalizedLebesgueSpectrum_compactification a ha
  have scaledIdentity :
      resolventCompactification a ha.ne' (lambda • normalizedLebesgueSpectrum) =
        (lambda * ENNReal.ofReal (1 / (2 * a))) •
          ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) := by
    rw [resolventCompactification_smul, baseIdentity, smul_smul]
  refine ⟨baseIdentity, scaledIdentity, ?_, ?_⟩
  · rw [← scaledIdentity]
    exact resolventCompactification_order_iff a ha
      (lambda • normalizedLebesgueSpectrum) nu
  · rw [resolventCompactification_smul,
      normalizedLebesgueSpectrum_compactification (1 / 2 : Real) (by norm_num), smul_smul]
    norm_num

#print axioms normalizedLebesgueSpectrum
#print axioms cayleyCircle
#print axioms resolventCompactification
#print axioms white_to_haar_identity

end D5.S3.Weil.Budget.WhiteToHaarIdentity
