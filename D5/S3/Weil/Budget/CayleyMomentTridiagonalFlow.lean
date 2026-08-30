/- GID: D5/S3/Weil/Budget/CayleyMomentTridiagonalFlow
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/CayleyMomentTridiagonalFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cayley moments satisfy the tridiagonal positive-scale flow and its resolvent-budget specialization. -/

import D5.S3.Weil.Budget.CayleyMomentTridiagonalFlowLemmas

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.CayleyMomentTridiagonalFlow

open CayleyScaleChange PositiveCayleyScaleTransport
open D5.S3.Weil.Budget.CayleyMomentTridiagonalFlowLemmas

theorem tridiagonal_moment_flow
    (source : Measure Real)
    (hEven : Measure.map (fun xi : Real => -xi) source = source)
    (hIntegrable : ∀ scale : Real, 0 < scale →
      Integrable (fun xi : Real => 1 / (xi ^ 2 + scale ^ 2)) source)
    (a : Real) (ha : 0 < a) :
    let moment : Nat → Real → Real := fun n scale =>
      (∫ z : Complex, z ^ n ∂cayleySpectralMeasure source scale).re
    let inverseFirst : Real → Real := fun scale =>
      (∫ z : Complex, z⁻¹ ∂cayleySpectralMeasure source scale).re
    let budget : Real → Real := fun scale =>
      ∫ xi : Real, 1 / (xi ^ 2 + scale ^ 2) ∂source
    (∀ scale : Real, 0 < scale → inverseFirst scale = moment 1 scale) ∧
      HasDerivAt (moment 0)
        ((((moment 1 a + inverseFirst a) / 2) - moment 0 a) / a) a ∧
      (∀ n : Nat, HasDerivAt (moment (n + 1))
        (((((n + 2 : Nat) : Real) / 2) * moment (n + 2) a +
          ((-(n : Real)) / 2) * moment n a - moment (n + 1) a) / a) a) ∧
      HasDerivAt budget ((moment 1 a - budget a) / a) a := by
  dsimp only
  have hsourceMomentIntegrable
      (scale : Real) (hscale : 0 < scale) (n : Nat) :
      Integrable (fun xi : Real => cayleyCoordinate scale xi ^ n /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)) source := by
    have hmeas : Measurable (fun xi : Real => cayleyCoordinate scale xi ^ n /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)) := by
      unfold cayleyCoordinate
      fun_prop
    refine (hIntegrable scale hscale).mono' hmeas.aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro xi
    have hdenpos : 0 < xi ^ 2 + scale ^ 2 := by positivity
    have hz : ‖cayleyCoordinate scale xi‖ = 1 := by
      unfold cayleyCoordinate
      rw [norm_div]
      have hden : ‖(xi : Complex) - Complex.I * (scale : Complex)‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        intro h
        have him := congrArg Complex.im h
        simp at him
        linarith
      have hnorm : ‖(xi : Complex) + Complex.I * (scale : Complex)‖ =
          ‖(xi : Complex) - Complex.I * (scale : Complex)‖ := by
        rw [Complex.norm_def, Complex.norm_def]
        congr 1
        simp [Complex.normSq_apply]
      rw [hnorm, div_self hden]
    rw [norm_div, norm_pow, hz, one_pow]
    rw [show ‖(xi : Complex) ^ 2 + (scale : Complex) ^ 2‖ =
        xi ^ 2 + scale ^ 2 by
      rw [show (xi : Complex) ^ 2 + (scale : Complex) ^ 2 =
        ((xi ^ 2 + scale ^ 2 : Real) : Complex) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]]
  have hsourceInverseIntegrable
      (scale : Real) (hscale : 0 < scale) :
      Integrable (fun xi : Real => (cayleyCoordinate scale xi)⁻¹ /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)) source := by
    have hmeas : Measurable (fun xi : Real => (cayleyCoordinate scale xi)⁻¹ /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)) := by
      unfold cayleyCoordinate
      fun_prop
    refine (hIntegrable scale hscale).mono' hmeas.aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro xi
    have hdenpos : 0 < xi ^ 2 + scale ^ 2 := by positivity
    have hz : ‖cayleyCoordinate scale xi‖ = 1 := by
      unfold cayleyCoordinate
      rw [norm_div]
      have hden : ‖(xi : Complex) - Complex.I * (scale : Complex)‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        intro h
        have him := congrArg Complex.im h
        simp at him
        linarith
      have hnorm : ‖(xi : Complex) + Complex.I * (scale : Complex)‖ =
          ‖(xi : Complex) - Complex.I * (scale : Complex)‖ := by
        rw [Complex.norm_def, Complex.norm_def]
        congr 1
        simp [Complex.normSq_apply]
      rw [hnorm, div_self hden]
    rw [norm_div, norm_inv, hz]
    rw [show ‖(xi : Complex) ^ 2 + (scale : Complex) ^ 2‖ =
        xi ^ 2 + scale ^ 2 by
      rw [show (xi : Complex) ^ 2 + (scale : Complex) ^ 2 =
        ((xi ^ 2 + scale ^ 2 : Real) : Complex) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]]
    simp only [inv_one]
    exact le_rfl
  have hconvention : ∀ scale : Real, 0 < scale →
      (∫ z : Complex, z⁻¹ ∂cayleySpectralMeasure source scale).re =
        (∫ z : Complex, z ^ (1 : Nat)
          ∂cayleySpectralMeasure source scale).re := by
    intro scale hscale
    apply congrArg Complex.re
    rw [canonical_inverse_moment_eq_source source scale hscale,
      canonical_nat_moment_eq_source source scale hscale 1]
    simpa only [pow_one] using source_inverse_first_eq_first source hEven scale hscale
  refine ⟨hconvention, ?_, ?_, ?_⟩
  · have hzeroSource := density_integral_hasDerivAt source hIntegrable a ha
    have hzeroCanonical : HasDerivAt
        (fun scale : Real => ∫ z : Complex, z ^ (0 : Nat)
          ∂cayleySpectralMeasure source scale)
        (∫ xi : Real, (1 / a : Real) *
          (((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
            ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) ∂source) a := by
      apply hzeroSource.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ha] with scale hscale
      rw [canonical_nat_moment_eq_source source scale hscale 0]
      simp only [pow_zero]
    have hzeroDerivative :
        (∫ xi : Real, (1 / a : Real) *
          (((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
            ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) ∂source) =
        ((1 / a : Real) : Complex) *
          (((∫ z : Complex, z ^ (1 : Nat) ∂cayleySpectralMeasure source a) +
              (∫ z : Complex, z⁻¹ ∂cayleySpectralMeasure source a)) / 2 -
            (∫ z : Complex, z ^ (0 : Nat)
              ∂cayleySpectralMeasure source a)) := by
      rw [canonical_nat_moment_eq_source source a ha 1,
        canonical_inverse_moment_eq_source source a ha,
        canonical_nat_moment_eq_source source a ha 0]
      simp only [pow_one, pow_zero]
      have hfirst : Integrable (fun xi : Real => cayleyCoordinate a xi /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) source := by
        simpa only [pow_one] using hsourceMomentIntegrable a ha 1
      have hinverse := hsourceInverseIntegrable a ha
      have hzero : Integrable (fun xi : Real => (1 : Complex) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) source := by
        simpa only [pow_zero] using hsourceMomentIntegrable a ha 0
      rw [integral_const_mul]
      congr 1
      rw [show
        ((∫ xi : Real, cayleyCoordinate a xi /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) +
            (∫ xi : Real, (cayleyCoordinate a xi)⁻¹ /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source)) / 2 =
          (2 : Complex)⁻¹ *
            ((∫ xi : Real, cayleyCoordinate a xi /
                ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) +
              (∫ xi : Real, (cayleyCoordinate a xi)⁻¹ /
                ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source)) by ring]
      rw [← integral_add hfirst hinverse, ← integral_const_mul]
      have haverage := (hfirst.add hinverse).const_mul (2 : Complex)⁻¹
      have haverage' : Integrable (fun xi : Real => (2 : Complex)⁻¹ *
          (cayleyCoordinate a xi / ((xi : Complex) ^ 2 + (a : Complex) ^ 2) +
            (cayleyCoordinate a xi)⁻¹ /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2))) source := by
        simpa only [Pi.add_apply] using haverage
      rw [← integral_sub haverage' hzero]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro xi
      ring
    have hzeroReal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a
      (hzeroCanonical.congr_deriv hzeroDerivative)
    apply hzeroReal.congr_deriv
    norm_num [Complex.mul_re, Complex.div_re, Complex.inv_re,
      Complex.normSq_apply]
    ring
  · intro n
    have hsuccessorSource :=
      successor_integral_hasDerivAt source hIntegrable n a ha
    have hsuccessorCanonical : HasDerivAt
        (fun scale : Real => ∫ z : Complex, z ^ (n + 1)
          ∂cayleySpectralMeasure source scale)
        (∫ xi : Real, (1 / a : Real) *
          ((((n + 2 : Nat) : Real) / 2 : Real) *
              cayleyCoordinate a xi ^ (n + 2) +
            ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
            cayleyCoordinate a xi ^ (n + 1)) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) a := by
      apply hsuccessorSource.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ha] with scale hscale
      rw [canonical_nat_moment_eq_source source scale hscale (n + 1)]
    have hsuccessorDerivative :
        (∫ xi : Real, (1 / a : Real) *
          ((((n + 2 : Nat) : Real) / 2 : Real) *
              cayleyCoordinate a xi ^ (n + 2) +
            ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
            cayleyCoordinate a xi ^ (n + 1)) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) =
        ((1 / a : Real) : Complex) *
          (((((n + 2 : Nat) : Real) / 2 : Real) : Complex) *
              (∫ z : Complex, z ^ (n + 2) ∂cayleySpectralMeasure source a) +
            (((( -(n : Real)) / 2 : Real) : Complex)) *
              (∫ z : Complex, z ^ n ∂cayleySpectralMeasure source a) -
            (∫ z : Complex, z ^ (n + 1)
              ∂cayleySpectralMeasure source a)) := by
      rw [canonical_nat_moment_eq_source source a ha (n + 2),
        canonical_nat_moment_eq_source source a ha n,
        canonical_nat_moment_eq_source source a ha (n + 1)]
      have hfactor :
          (∫ xi : Real, (1 / a : Real) *
            ((((n + 2 : Nat) : Real) / 2 : Real) *
                cayleyCoordinate a xi ^ (n + 2) +
              ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
              cayleyCoordinate a xi ^ (n + 1)) /
            ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) =
          ((1 / a : Real) : Complex) *
            (∫ xi : Real,
              ((((n + 2 : Nat) : Real) / 2 : Real) *
                  cayleyCoordinate a xi ^ (n + 2) +
                ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
                cayleyCoordinate a xi ^ (n + 1)) /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro xi
        ring
      rw [hfactor]
      congr 1
      let A : Complex := (((n + 2 : Nat) : Real) / 2 : Real)
      let B : Complex := ((-(n : Real)) / 2 : Real)
      let fA : Real → Complex := fun xi => cayleyCoordinate a xi ^ (n + 2) /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2)
      let fB : Real → Complex := fun xi => cayleyCoordinate a xi ^ n /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2)
      let fC : Real → Complex := fun xi => cayleyCoordinate a xi ^ (n + 1) /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2)
      have hfA : Integrable fA source := hsourceMomentIntegrable a ha (n + 2)
      have hfB : Integrable fB source := hsourceMomentIntegrable a ha n
      have hfC : Integrable fC source := hsourceMomentIntegrable a ha (n + 1)
      have hscaledA : Integrable (fun xi => A * fA xi) source := hfA.const_mul A
      have hscaledB : Integrable (fun xi => B * fB xi) source := hfB.const_mul B
      have hsum : Integrable (fun xi => A * fA xi + B * fB xi) source :=
        hscaledA.add hscaledB
      calc
        (∫ xi : Real,
            ((((n + 2 : Nat) : Real) / 2 : Real) *
                cayleyCoordinate a xi ^ (n + 2) +
              ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
              cayleyCoordinate a xi ^ (n + 1)) /
            ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) =
          ∫ xi : Real, A * fA xi + B * fB xi - fC xi ∂source := by
            apply integral_congr_ae
            apply Filter.Eventually.of_forall
            intro xi
            dsimp only [A, B, fA, fB, fC]
            ring
        _ = (∫ xi : Real, A * fA xi + B * fB xi ∂source) -
            ∫ xi : Real, fC xi ∂source := by
              simpa only [Pi.sub_apply] using integral_sub hsum hfC
        _ = ((∫ xi : Real, A * fA xi ∂source) +
              ∫ xi : Real, B * fB xi ∂source) -
            ∫ xi : Real, fC xi ∂source := by
              rw [integral_add hscaledA hscaledB]
        _ = A * (∫ xi : Real, fA xi ∂source) +
            B * (∫ xi : Real, fB xi ∂source) -
            ∫ xi : Real, fC xi ∂source := by
              rw [integral_const_mul, integral_const_mul]
        _ = _ := by rfl
    have hsuccessorReal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a
      (hsuccessorCanonical.congr_deriv hsuccessorDerivative)
    apply hsuccessorReal.congr_deriv
    norm_num [Complex.mul_re]
    ring
  · have hzeroSource := density_integral_hasDerivAt source hIntegrable a ha
    have hzeroSourceReal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hzeroSource
    have hbudgetReal (scale : Real) (hscale : 0 < scale) :
        (∫ xi : Real, (1 : Complex) /
          ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source).re =
        ∫ xi : Real, 1 / (xi ^ 2 + scale ^ 2) ∂source := by
      calc
        (∫ xi : Real, (1 : Complex) /
            ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source).re =
          (∫ z : Complex, z ^ (0 : Nat)
            ∂cayleySpectralMeasure source scale).re := by
              apply congrArg Complex.re
              simpa only [pow_zero] using
                (canonical_nat_moment_eq_source source scale hscale 0).symm
        _ = _ := canonical_zero_moment_eq_budget source scale hscale
    have hbudgetDeriv : HasDerivAt
        (fun scale : Real => ∫ xi : Real,
          1 / (xi ^ 2 + scale ^ 2) ∂source)
        (∫ xi : Real, (1 / a : Real) *
          (((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
            ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) ∂source).re a := by
      apply hzeroSourceReal.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ha] with scale hscale
      exact (hbudgetReal scale hscale).symm
    have hzeroComplexBudget :
        (∫ xi : Real, (1 : Complex) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) =
        ((∫ xi : Real, 1 / (xi ^ 2 + a ^ 2) ∂source : Real) : Complex) := by
      calc
        (∫ xi : Real, (1 : Complex) /
            ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) =
          ∫ xi : Real, ((1 / (xi ^ 2 + a ^ 2) : Real) : Complex) ∂source := by
            apply integral_congr_ae
            apply Filter.Eventually.of_forall
            intro xi
            have hdenpos : 0 < xi ^ 2 + a ^ 2 := by positivity
            push_cast
            field_simp [hdenpos.ne']
        _ = _ := integral_ofReal
    have hspecialDerivative :
        (∫ xi : Real, (1 / a : Real) *
          (((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
            ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) ∂source) =
        ((1 / a : Real) : Complex) *
          ((∫ z : Complex, z ^ (1 : Nat)
              ∂cayleySpectralMeasure source a) -
            ((∫ xi : Real, 1 / (xi ^ 2 + a ^ 2) ∂source : Real) : Complex)) := by
      rw [canonical_nat_moment_eq_source source a ha 1]
      simp only [pow_one]
      rw [← hzeroComplexBudget]
      have hfirst : Integrable (fun xi : Real => cayleyCoordinate a xi /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) source := by
        simpa only [pow_one] using hsourceMomentIntegrable a ha 1
      have hinverse := hsourceInverseIntegrable a ha
      have hzero : Integrable (fun xi : Real => (1 : Complex) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) source := by
        simpa only [pow_zero] using hsourceMomentIntegrable a ha 0
      rw [integral_const_mul]
      congr 1
      calc
        (∫ xi : Real,
            ((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) =
          ((∫ xi : Real, cayleyCoordinate a xi /
                ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) +
            (∫ xi : Real, (cayleyCoordinate a xi)⁻¹ /
                ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source)) / 2 -
            ∫ xi : Real, (1 : Complex) /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source := by
          have haverage : Integrable (fun xi : Real => (2 : Complex)⁻¹ *
              (cayleyCoordinate a xi /
                  ((xi : Complex) ^ 2 + (a : Complex) ^ 2) +
                (cayleyCoordinate a xi)⁻¹ /
                  ((xi : Complex) ^ 2 + (a : Complex) ^ 2))) source :=
            (hfirst.add hinverse).const_mul (2 : Complex)⁻¹
          rw [show
            ((∫ xi : Real, cayleyCoordinate a xi /
                  ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) +
              (∫ xi : Real, (cayleyCoordinate a xi)⁻¹ /
                  ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source)) / 2 =
              ∫ xi : Real, (2 : Complex)⁻¹ *
                (cayleyCoordinate a xi /
                    ((xi : Complex) ^ 2 + (a : Complex) ^ 2) +
                  (cayleyCoordinate a xi)⁻¹ /
                    ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) ∂source by
              rw [integral_const_mul, integral_add hfirst hinverse]
              ring]
          rw [← integral_sub haverage hzero]
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro xi
          ring
        _ = (∫ xi : Real, cayleyCoordinate a xi /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) -
            ∫ xi : Real, (1 : Complex) /
              ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source := by
          rw [source_inverse_first_eq_first source hEven a ha]
          ring
    apply hbudgetDeriv.congr_deriv
    rw [hspecialDerivative]
    norm_num [Complex.mul_re]
    ring

#print axioms tridiagonal_moment_flow

end D5.S3.Weil.Budget.CayleyMomentTridiagonalFlow
