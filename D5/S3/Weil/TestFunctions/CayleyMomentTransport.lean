/- GID: D5/S3/Weil/TestFunctions/CayleyMomentTransport
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/CayleyMomentTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transport local Fourier moments through resolvent Cayley compactification. -/

import D5.S3.Weil.Budget.FullCirclePrimalAttainment
import D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/- Library-search audit trail (2026-08-29):
   * D5 searches found the canonical `WeilTestFunction`, `fourierLaplace`,
     `cayleyCharacter`, and `normalizedCircleHaar`; they are imported rather
     than redeclared.
   * Body-shape searches for the weighted Cayley pushforward, its inverse
     coordinate, and the resulting moment function found no D5 owner.
   * Pinned Mathlib has no exact Cayley/Haar transport theorem. The proof uses
     `integral_withDensity_eq_integral_smul`, one-dimensional Jacobian change
     of variables, normalized additive-circle Haar integration, and Schwartz
     Fourier inversion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal FourierTransform
open D5.S3.Weil.Budget.FullCirclePrimalAttainment
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity

namespace D5.S3.Weil.TestFunctions.CayleyMomentTransport

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

private theorem cayley_denominator_ne_zero {a xi : Real} (ha : 0 < a) :
    ((xi : Complex) - Complex.I * a) ≠ 0 := by
  intro h
  have himaginary := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re] at himaginary
  norm_num at himaginary
  linarith

/-- The source Cayley character, bundled on the exact complex unit circle. -/
noncomputable def cayleyCircle (a : Real) (ha : 0 < a) (xi : Real) : Circle := by
  refine ⟨cayleyCharacter a xi, ?_⟩
  change cayleyCharacter a xi ∈ Metric.sphere (0 : Complex) 1
  rw [mem_sphere_zero_iff_norm]
  rw [cayleyCharacter, norm_div]
  have hequal :
      ‖(xi : Complex) + Complex.I * a‖ =
        ‖(xi : Complex) - Complex.I * a‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul,
      Complex.add_im, Complex.ofReal_im, zero_add, Complex.sub_re,
      Complex.sub_im, zero_sub]
    ring
  rw [hequal, div_self (norm_ne_zero_iff.mpr (cayley_denominator_ne_zero ha))]

/-- The positive resolvent density used before the Cayley pushforward. -/
noncomputable def resolventDensity (a xi : Real) : NNReal :=
  ⟨(xi ^ 2 + a ^ 2)⁻¹, by positivity⟩

/-- Resolvent-weighted Cayley compactification of a positive real-line measure. -/
noncomputable def cayleyCompactification
    (a : Real) (ha : 0 < a) (nu : Measure Real) : Measure Circle :=
  Measure.map (cayleyCircle a ha)
    (nu.withDensity fun xi => (resolventDensity a xi : ENNReal))

/-- The real Cayley inverse coordinate, totalized at the omitted circle point. -/
noncomputable def cayleyInverse (a : Real) (z : Circle) : Real :=
  (Complex.I * a * ((z : Complex) + 1) / ((z : Complex) - 1)).re

/-- The local Fourier moment function on the circle, with its flat value at infinity. -/
noncomputable def cayleyMomentFunction
    (a : Real) (phi : WeilTestFunction) (z : Circle) : Complex := by
  classical
  exact if z = 1 then 0
    else ((cayleyInverse a z) ^ 2 + a ^ 2 : Real) *
      fourierLaplace phi (cayleyInverse a z)

/-- Pairing of the inverse spectral distribution with a local Weil test. -/
noncomputable def inverseMeasurePairing
    (nu : Measure Real) (phi : WeilTestFunction) : Complex :=
  ∫ xi : Real, fourierLaplace phi xi ∂nu

private theorem cayley_circle_ne_one {a xi : Real} (ha : 0 < a) :
    cayleyCircle a ha xi ≠ 1 := by
  intro h
  have hcomplex : cayleyCharacter a xi = (1 : Complex) := congrArg Subtype.val h
  rw [cayleyCharacter, div_eq_one_iff_eq (cayley_denominator_ne_zero ha)] at hcomplex
  have himaginary := congrArg Complex.im hcomplex
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, zero_add, one_mul, Complex.sub_im,
    zero_sub] at himaginary
  linarith

private theorem cayley_inverse_apply {a xi : Real} (ha : 0 < a) :
    cayleyInverse a (cayleyCircle a ha xi) = xi := by
  rw [cayleyInverse]
  change
    (Complex.I * a * (cayleyCharacter a xi + 1) /
      (cayleyCharacter a xi - 1)).re = xi
  have hcomplex :
      Complex.I * a * (cayleyCharacter a xi + 1) /
          (cayleyCharacter a xi - 1) =
        (xi : Complex) := by
    rw [cayleyCharacter]
    field_simp [cayley_denominator_ne_zero ha]
    have hdifference :
        (xi : Complex) + Complex.I * a - ((xi : Complex) - Complex.I * a) ≠ 0 := by
      rw [show (xi : Complex) + Complex.I * a - ((xi : Complex) - Complex.I * a) =
        2 * Complex.I * a by ring]
      exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr ha.ne')
    apply (div_eq_iff hdifference).2
    ring_nf
  rw [hcomplex]
  simp

private theorem cayley_moment_apply {a xi : Real} (ha : 0 < a)
    (phi : WeilTestFunction) :
    cayleyMomentFunction a phi (cayleyCircle a ha xi) =
      ((xi ^ 2 + a ^ 2 : Real) : Complex) * fourierLaplace phi xi := by
  rw [cayleyMomentFunction, if_neg (cayley_circle_ne_one ha), cayley_inverse_apply ha]

private theorem continuous_cayley_circle {a : Real} (ha : 0 < a) :
    Continuous (cayleyCircle a ha) := by
  apply Continuous.subtype_mk
  change Continuous (fun xi : Real => cayleyCharacter a xi)
  unfold cayleyCharacter
  exact Continuous.div (by fun_prop) (by fun_prop)
    (fun xi => cayley_denominator_ne_zero ha)

private theorem continuous_fourier_laplace_real (phi : WeilTestFunction) :
    Continuous (fun xi : Real => fourierLaplace phi xi) := by
  let schwartz : SchwartzMap Real Complex :=
    phi.hasCompactSupport.toSchwartzMap phi.contDiff
  have hcontinuous :
      Continuous (fun xi : Real => (𝓕 schwartz) (mathlibFrequency xi)) :=
    (𝓕 schwartz).continuous.comp (by
      unfold mathlibFrequency
      fun_prop)
  convert hcontinuous using 1
  ext xi
  rw [fourierLaplace_real_eq_fourier]
  rfl

private theorem measurable_cayley_moment_function
    (a : Real) (phi : WeilTestFunction) :
    Measurable (cayleyMomentFunction a phi) := by
  classical
  unfold cayleyMomentFunction cayleyInverse
  apply Measurable.ite (measurableSet_singleton (1 : Circle)) measurable_const
  have hinverse : Measurable fun z : Circle =>
      (Complex.I * a * ((z : Complex) + 1) / ((z : Complex) - 1)).re := by
    fun_prop
  have hfourier : Measurable fun z : Circle =>
      fourierLaplace phi
        (Complex.I * a * ((z : Complex) + 1) / ((z : Complex) - 1)).re :=
    (continuous_fourier_laplace_real phi).measurable.comp hinverse
  fun_prop

private theorem measurable_resolvent_density (a : Real) :
    Measurable (resolventDensity a) := by
  unfold resolventDensity
  fun_prop

private theorem transported_moment
    (a : Real) (ha : 0 < a) (nu : Measure Real) (phi : WeilTestFunction) :
    ∫ z : Circle, cayleyMomentFunction a phi z ∂cayleyCompactification a ha nu =
      ∫ xi : Real, fourierLaplace phi xi ∂nu := by
  rw [cayleyCompactification]
  rw [integral_map
    (continuous_cayley_circle ha).measurable.aemeasurable
    (measurable_cayley_moment_function a phi).aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_smul (measurable_resolvent_density a)]
  apply integral_congr_ae
  filter_upwards with xi
  rw [cayley_moment_apply ha]
  change
    (resolventDensity a xi : Real) •
      ((xi ^ 2 + a ^ 2 : Real) • fourierLaplace phi xi) =
        fourierLaplace phi xi
  rw [smul_smul]
  have hscalar : (resolventDensity a xi : Real) * (xi ^ 2 + a ^ 2) = 1 := by
    change (xi ^ 2 + a ^ 2)⁻¹ * (xi ^ 2 + a ^ 2) = 1
    field_simp [show xi ^ 2 + a ^ 2 ≠ 0 by positivity]
  rw [hscalar, one_smul]

private theorem integral_fourier_laplace
    (phi : WeilTestFunction) :
    (∫ xi : Real, fourierLaplace phi xi) =
      (2 * Real.pi : Real) • phi 0 := by
  let schwartz : SchwartzMap Real Complex :=
    phi.hasCompactSupport.toSchwartzMap phi.contDiff
  have hinversion : (∫ v : Real, (𝓕 schwartz) v) = schwartz 0 := by
    have h := congrArg (fun f : SchwartzMap Real Complex => f 0)
      (FourierTransform.fourierInv_fourier_eq
        (E := SchwartzMap Real Complex) (F := SchwartzMap Real Complex) schwartz)
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
    simpa [Real.inner_apply] using h
  have hscale := Measure.integral_comp_inv_mul_left
    (fun w : Real => (𝓕 schwartz) w) (2 * Real.pi)
  rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hscale
  calc
    (∫ xi : Real, fourierLaplace phi xi) =
        ∫ xi : Real, (𝓕 schwartz) ((2 * Real.pi)⁻¹ * xi) := by
          apply integral_congr_ae
          filter_upwards with xi
          rw [fourierLaplace_real_eq_fourier]
          rw [show mathlibFrequency xi = (2 * Real.pi)⁻¹ * xi by
            unfold mathlibFrequency
            ring]
          exact congrFun (SchwartzMap.fourier_coe schwartz).symm _
    _ = (2 * Real.pi : Real) • ∫ w : Real, (𝓕 schwartz) w := hscale
    _ = (2 * Real.pi : Real) • phi 0 := by
      rw [hinversion]
      rfl

private theorem angle_cayley_apply {a xi : Real} (ha : 0 < a) :
    Circle.exp (Real.pi - 2 * Real.arctan (xi / a)) = cayleyCircle a ha xi := by
  let t : Real := xi / a
  have htden : 1 + t ^ 2 ≠ 0 := by positivity
  have hcos : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    field_simp [htden]
    ring
  have hsin : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hsqrt : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
    field_simp [hsqrt]
    rw [Real.sq_sqrt (by positivity)]
  apply Circle.ext
  rw [Circle.coe_exp, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  change
    ((Real.cos (Real.pi - 2 * Real.arctan (xi / a)) : Real) : Complex) +
        Real.sin (Real.pi - 2 * Real.arctan (xi / a)) * Complex.I =
      cayleyCharacter a xi
  rw [Real.cos_pi_sub, Real.sin_pi_sub, hcos, hsin]
  rw [cayleyCharacter]
  dsimp only [t]
  push_cast
  field_simp [cayley_denominator_ne_zero ha, htden, ha.ne']
  have hsum : ((a : Complex) ^ 2 + (xi : Complex) ^ 2) ≠ 0 := by
    exact_mod_cast (show a ^ 2 + xi ^ 2 ≠ 0 by positivity)
  have hright : (xi : Complex) - (a : Complex) * Complex.I ≠ 0 := by
    simpa [mul_comm] using cayley_denominator_ne_zero (xi := xi) ha
  field_simp [hsum, hright]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem angle_coordinate_derivative {a xi : Real} (ha : 0 < a) :
    HasDerivAt (fun x : Real => Real.pi - 2 * Real.arctan (x / a))
      (-2 * a / (xi ^ 2 + a ^ 2)) xi := by
  have hbase := (Real.hasDerivAt_arctan (xi / a)).comp xi
      ((hasDerivAt_id xi).div_const a) |>.const_mul 2 |>.const_sub Real.pi
  have hvalue :
      -(2 * ((1 / (1 + (xi / a) ^ 2)) * (1 / a))) =
        -2 * a / (xi ^ 2 + a ^ 2) := by
    field_simp [ha.ne', show xi ^ 2 + a ^ 2 ≠ 0 by positivity]
    ring
  exact hbase.congr_deriv hvalue

private theorem angle_coordinate_injective {a : Real} (ha : 0 < a) :
    Function.Injective (fun xi : Real => Real.pi - 2 * Real.arctan (xi / a)) := by
  intro x y h
  have harctan : Real.arctan (x / a) = Real.arctan (y / a) := by linarith
  have hdivision : x / a = y / a := Real.arctan_injective harctan
  exact (div_left_inj' ha.ne').mp hdivision

private theorem angle_coordinate_range {a : Real} (ha : 0 < a) :
    Set.range (fun xi : Real => Real.pi - 2 * Real.arctan (xi / a)) =
      Set.Ioo 0 (2 * Real.pi) := by
  ext theta
  constructor
  · rintro ⟨xi, rfl⟩
    rcases Real.arctan_mem_Ioo (xi / a) with ⟨hlower, hupper⟩
    constructor <;> dsimp <;> linarith [Real.pi_pos]
  · intro htheta
    have hangle : (Real.pi - theta) / 2 ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [htheta.1, htheta.2]
    rw [← Real.range_arctan] at hangle
    obtain ⟨x, hx⟩ := hangle
    refine ⟨a * x, ?_⟩
    change Real.pi - 2 * Real.arctan (a * x / a) = theta
    rw [show a * x / a = x by field_simp, hx]
    ring

private theorem haar_moment
    (a : Real) (ha : 0 < a) (phi : WeilTestFunction) :
    ∫ z : Circle, cayleyMomentFunction a phi z
        ∂(normalizedCircleHaar : Measure Circle) =
      ((2 * a : Real) : Complex) * phi 0 := by
  let angleMoment : Real -> Complex := fun theta =>
    cayleyMomentFunction a phi (Circle.exp theta)
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ)
    (f := fun xi : Real => Real.pi - 2 * Real.arctan (xi / a))
    (f' := fun xi : Real => -2 * a / (xi ^ 2 + a ^ 2))
    MeasurableSet.univ
    (fun xi _ => (angle_coordinate_derivative ha).hasDerivWithinAt)
    (angle_coordinate_injective ha).injOn
    angleMoment
  rw [Set.image_univ, angle_coordinate_range ha] at hchange
  have hchange' :
      (∫ theta in Set.Ioc 0 (2 * Real.pi), angleMoment theta) =
        (2 * a : Real) • ∫ xi : Real, fourierLaplace phi xi := by
    calc
      (∫ theta in Set.Ioc 0 (2 * Real.pi), angleMoment theta) =
          ∫ theta in Set.Ioo 0 (2 * Real.pi), angleMoment theta := by
            rw [integral_Ioc_eq_integral_Ioo]
      _ = ∫ xi : Real,
          |-2 * a / (xi ^ 2 + a ^ 2)| •
            angleMoment (Real.pi - 2 * Real.arctan (xi / a)) := by
        simpa only [setIntegral_univ] using hchange
      _ = ∫ xi : Real, (2 * a : Real) • fourierLaplace phi xi := by
        apply integral_congr_ae
        filter_upwards with xi
        rw [show angleMoment (Real.pi - 2 * Real.arctan (xi / a)) =
            cayleyMomentFunction a phi (cayleyCircle a ha xi) by
          dsimp only [angleMoment]
          rw [angle_cayley_apply ha]]
        rw [cayley_moment_apply ha, abs_of_neg
          (div_neg_of_neg_of_pos (by linarith) (by positivity))]
        rw [show -(-2 * a / (xi ^ 2 + a ^ 2)) =
          2 * a / (xi ^ 2 + a ^ 2) by ring]
        change
          (2 * a / (xi ^ 2 + a ^ 2) : Real) •
              ((xi ^ 2 + a ^ 2 : Real) • fourierLaplace phi xi) =
            (2 * a : Real) • fourierLaplace phi xi
        rw [smul_smul]
        congr 1
        field_simp [show xi ^ 2 + a ^ 2 ≠ 0 by positivity]
      _ = (2 * a : Real) • ∫ xi : Real, fourierLaplace phi xi :=
        integral_smul (2 * a) (fun xi : Real => fourierLaplace phi xi)
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hhaar :
      ((normalizedCircleHaar : FiniteMeasure Circle) : Measure Circle) =
        Measure.map AddCircle.homeomorphCircle' AddCircle.haarAddCircle := by
    rw [normalizedCircleHaar]
    rfl
  rw [hhaar]
  rw [integral_map
    AddCircle.homeomorphCircle'.continuous.measurable.aemeasurable
    (measurable_cayley_moment_function a phi).aestronglyMeasurable]
  change
    (∫ theta : AddCircle (2 * Real.pi),
      cayleyMomentFunction a phi (AddCircle.homeomorphCircle' theta)
        ∂AddCircle.haarAddCircle) = _
  rw [AddCircle.integral_haarAddCircle]
  rw [← AddCircle.integral_preimage (2 * Real.pi) 0]
  simp only [zero_add]
  have hpreimage :
      (fun theta : Real =>
        cayleyMomentFunction a phi
          (AddCircle.homeomorphCircle' (theta : AddCircle (2 * Real.pi)))) =
        angleMoment := by
    funext theta
    dsimp only [angleMoment]
    rw [AddCircle.homeomorphCircle'_apply_mk]
  rw [hpreimage, hchange', integral_fourier_laplace]
  change
    (2 * Real.pi)⁻¹ • ((2 * a : Real) • ((2 * Real.pi : Real) • phi 0)) =
      ((2 * a : Real) : Complex) * phi 0
  rw [smul_smul, smul_smul]
  change
    ((((2 * Real.pi)⁻¹ * (2 * a) * (2 * Real.pi) : Real) : Complex) * phi 0) =
      ((2 * a : Real) : Complex) * phi 0
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Local Fourier moments, their inverse-distribution pairing, and the Haar
moment are transported by the resolvent Cayley compactification. -/
theorem cayley_moment_transport
    (a : Real) (ha : 0 < a) (nu : Measure Real) (phi : WeilTestFunction) :
    (∫ z : Circle, cayleyMomentFunction a phi z ∂cayleyCompactification a ha nu =
      ∫ xi : Real, fourierLaplace phi xi ∂nu) ∧
    (∫ z : Circle, cayleyMomentFunction a phi z ∂cayleyCompactification a ha nu =
      inverseMeasurePairing nu phi) ∧
    (∫ z : Circle, cayleyMomentFunction a phi z
        ∂(normalizedCircleHaar : Measure Circle) =
      ((2 * a : Real) : Complex) * phi 0) := by
  have htransport := transported_moment a ha nu phi
  exact ⟨htransport, by simpa [inverseMeasurePairing] using htransport,
    haar_moment a ha phi⟩

#print axioms cayley_moment_transport

end D5.S3.Weil.TestFunctions.CayleyMomentTransport
