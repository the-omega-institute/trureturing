/- GID: D5/S3/Weil/Budget/CayleyMomentTridiagonalFlowLemmas
   generality: G
   mirror-B: none(waiver:internal-tridiagonal-flow-proof-support)
   mirror-E: none(waiver:kernel-proof-support-in-formal-module)
   anchors: []
   digest: Internal analytic support for the Cayley moment tridiagonal flow. -/

import D5.S3.Weil.Budget.LinearCayleyScaleFlow

/- Library-search audit trail (2026-08-31):
   * D5 body-shape searches found the canonical `cayleyCoordinate`,
     `resolventWeightedMeasure`, and `cayleySpectralMeasure` primitives, but
     no moment-scale derivative or tridiagonal recurrence owner.
   * Pinned Mathlib supplies dominated differentiation under an integral and
     integration against an ENNReal density, but no exact Cayley moment flow.
   * The source's evenness and positive-scale resolvent integrability are
     explicit hypotheses; the moment and budget are constructed from the
     canonical scale-dependent spectral measure and source measure. -/

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.CayleyMomentTridiagonalFlowLemmas

open CayleyScaleChange PositiveCayleyScaleTransport

theorem coordinate_hasDerivAt (xi a : Real) (ha : 0 < a) :
    HasDerivAt (fun scale : Real => cayleyCoordinate scale xi)
      (-((1 - cayleyCoordinate a xi ^ 2) / (2 * a))) a := by
  have hcast : HasDerivAt (fun scale : Real => (scale : Complex)) 1 a :=
    Complex.ofRealCLM.hasDerivAt
  have himag : HasDerivAt (fun scale : Real => Complex.I * (scale : Complex)) Complex.I a := by
    simpa using hcast.const_mul Complex.I
  have hnum := (hasDerivAt_const a (xi : Complex)).add himag
  have hden := (hasDerivAt_const a (xi : Complex)).sub himag
  have hdenNe : (xi : Complex) - Complex.I * (a : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  unfold cayleyCoordinate
  apply (hnum.div hden (by simpa only [Pi.sub_apply] using hdenNe)).congr_deriv
  simp only [Pi.add_apply, Pi.sub_apply, zero_add, zero_sub]
  field_simp [hdenNe, ha.ne']
  ring

theorem density_flow_identity (xi a : Real) (ha : 0 < a) :
    (a : Complex) * (-2 * (a : Complex) /
        (((xi : Complex) ^ 2 + (a : Complex) ^ 2) ^ 2)) =
      ((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2) := by
  have hplus : (xi : Complex) + Complex.I * (a : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hminus : (xi : Complex) - Complex.I * (a : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hden : (xi : Complex) ^ 2 + (a : Complex) ^ 2 ≠ 0 := by
    exact_mod_cast (by positivity : xi ^ 2 + a ^ 2 ≠ 0)
  have hden' : (a : Complex) ^ 2 + (xi : Complex) ^ 2 ≠ 0 := by
    simpa only [add_comm] using hden
  unfold cayleyCoordinate
  field_simp [hplus, hminus, hden, hden']
  ring_nf
  field_simp [hden']
  simp only [Complex.I_sq]
  ring

theorem density_integrand_hasDerivAt (xi a : Real) (ha : 0 < a) :
    HasDerivAt
      (fun scale : Real => 1 /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2))
      ((1 / a : Real) *
        (((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2))) a := by
  have hcast : HasDerivAt (fun scale : Real => (scale : Complex)) 1 a :=
    Complex.ofRealCLM.hasDerivAt
  have hden :=
    (hasDerivAt_const a ((xi : Complex) ^ 2)).add (hcast.pow 2)
  have hdenNe : (xi : Complex) ^ 2 + (a : Complex) ^ 2 ≠ 0 := by
    exact_mod_cast (by positivity : xi ^ 2 + a ^ 2 ≠ 0)
  have hone : HasDerivAt (fun _scale : Real => (1 : Complex)) 0 a :=
    hasDerivAt_const a 1
  have hdensity := hone.div hden hdenNe
  change HasDerivAt
    (fun scale : Real => 1 /
      ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)) _ a at hdensity
  apply hdensity.congr_deriv
  have hflow := density_flow_identity xi a ha
  simp only [Pi.add_apply, Pi.pow_apply, zero_mul, one_mul, zero_sub,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_add]
  calc
    -(2 * (a : Complex)) /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ^ 2 =
      ((1 / a : Real) : Complex) *
        ((a : Complex) * (-2 * (a : Complex) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ^ 2)) := by
            push_cast
            field_simp [ha.ne']
    _ = _ := by rw [hflow]

theorem successor_integrand_hasDerivAt (xi a : Real) (n : Nat) (ha : 0 < a) :
    HasDerivAt
      (fun scale : Real =>
        cayleyCoordinate scale xi ^ (n + 1) /
          ((xi : Complex) ^ 2 + (scale : Complex) ^ 2))
      ((1 / a : Real) *
        ((((n + 2 : Nat) : Real) / 2 : Real) *
            cayleyCoordinate a xi ^ (n + 2) +
          ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
          cayleyCoordinate a xi ^ (n + 1)) /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) a := by
  have hdenNe : (xi : Complex) ^ 2 + (a : Complex) ^ 2 ≠ 0 := by
    exact_mod_cast (by positivity : xi ^ 2 + a ^ 2 ≠ 0)
  have hzNe : cayleyCoordinate a xi ≠ 0 := by
    unfold cayleyCoordinate
    apply div_ne_zero
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
  have hcoord := coordinate_hasDerivAt xi a ha
  have hpow := hcoord.pow (n + 1)
  have hdensity' := density_integrand_hasDerivAt xi a ha
  have hproduct := hpow.mul hdensity'
  change HasDerivAt
    (fun scale : Real => cayleyCoordinate scale xi ^ (n + 1) *
      (1 / ((xi : Complex) ^ 2 + (scale : Complex) ^ 2))) _ a at hproduct
  simp only [one_div] at hproduct
  have hresult : HasDerivAt
      (fun scale : Real => cayleyCoordinate scale xi ^ (n + 1) *
        (((xi : Complex) ^ 2 + (scale : Complex) ^ 2)⁻¹))
      ((1 / a : Real) *
        ((((n + 2 : Nat) : Real) / 2 : Real) *
            cayleyCoordinate a xi ^ (n + 2) +
          ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
          cayleyCoordinate a xi ^ (n + 1)) /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) a := by
    apply hproduct.congr_deriv
    simp only [Pi.pow_apply]
    rw [show n + 1 - 1 = n by omega]
    push_cast
    field_simp [hdenNe, ha.ne', hzNe]
    ring
  apply hresult.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro scale
  change cayleyCoordinate scale xi ^ (n + 1) /
      ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) = _
  exact div_eq_mul_inv _ _

theorem successor_derivative_norm_le
    (xi scale a : Real) (n : Nat) (ha : 0 < a) (hscale : a / 2 < scale) :
    ‖((1 / scale : Real) *
        ((((n + 2 : Nat) : Real) / 2 : Real) *
            cayleyCoordinate scale xi ^ (n + 2) +
          ((-(n : Real)) / 2 : Real) * cayleyCoordinate scale xi ^ n -
          cayleyCoordinate scale xi ^ (n + 1)) /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2))‖ ≤
      (2 * ((n + 2 : Nat) : Real) / a) *
        (1 / (xi ^ 2 + (a / 2) ^ 2)) := by
  have hhalf : 0 < a / 2 := by positivity
  have hspos : 0 < scale := hhalf.trans hscale
  have hdenpos : 0 < xi ^ 2 + scale ^ 2 := by positivity
  have hhalfdenpos : 0 < xi ^ 2 + (a / 2) ^ 2 := by positivity
  have hz : ‖cayleyCoordinate scale xi‖ = 1 := by
    unfold cayleyCoordinate
    rw [norm_div]
    have hden : ‖(xi : Complex) - Complex.I * (scale : Complex)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hnorm :
        ‖(xi : Complex) + Complex.I * (scale : Complex)‖ =
          ‖(xi : Complex) - Complex.I * (scale : Complex)‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
    rw [hnorm, div_self hden]
  let A : Complex := (((n + 2 : Nat) : Real) / 2 : Real)
  let B : Complex := ((-(n : Real)) / 2 : Real)
  have hnum :
      ‖((((n + 2 : Nat) : Real) / 2 : Real) *
            cayleyCoordinate scale xi ^ (n + 2) +
          ((-(n : Real)) / 2 : Real) * cayleyCoordinate scale xi ^ n -
          cayleyCoordinate scale xi ^ (n + 1))‖ ≤
        ((n + 2 : Nat) : Real) := by
    change ‖A * cayleyCoordinate scale xi ^ (n + 2) +
      B * cayleyCoordinate scale xi ^ n -
      cayleyCoordinate scale xi ^ (n + 1)‖ ≤ ((n + 2 : Nat) : Real)
    calc
      ‖A * cayleyCoordinate scale xi ^ (n + 2) +
            B * cayleyCoordinate scale xi ^ n -
            cayleyCoordinate scale xi ^ (n + 1)‖ ≤
          ‖A * cayleyCoordinate scale xi ^ (n + 2)‖ +
            ‖B * cayleyCoordinate scale xi ^ n‖ +
            ‖cayleyCoordinate scale xi ^ (n + 1)‖ := by
              calc
                ‖_ - _‖ ≤ ‖_ + _‖ + ‖cayleyCoordinate scale xi ^ (n + 1)‖ :=
                  norm_sub_le _ _
                _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ = ((n + 2 : Nat) : Real) := by
        simp only [A, B, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, hz,
          one_pow, mul_one]
        rw [abs_of_nonneg (by positivity : 0 ≤ ((n + 2 : Nat) : Real) / 2),
          abs_of_nonpos (by
            have hn : 0 ≤ (n : Real) := Nat.cast_nonneg n
            linarith : (-(n : Real)) / 2 ≤ 0)]
        push_cast
        ring
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hspos)]
  rw [show ‖(xi : Complex) ^ 2 + (scale : Complex) ^ 2‖ =
      xi ^ 2 + scale ^ 2 by
        rw [show (xi : Complex) ^ 2 + (scale : Complex) ^ 2 =
          ((xi ^ 2 + scale ^ 2 : Real) : Complex) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]]
  calc
    (1 / scale *
        (‖((((n + 2 : Nat) : Real) / 2 : Real) *
              cayleyCoordinate scale xi ^ (n + 2) +
            ((-(n : Real)) / 2 : Real) * cayleyCoordinate scale xi ^ n -
            cayleyCoordinate scale xi ^ (n + 1))‖)) /
          (xi ^ 2 + scale ^ 2) ≤
      1 / scale * (((n + 2 : Nat) : Real) / (xi ^ 2 + scale ^ 2)) := by
        rw [mul_div_assoc]
        gcongr
    _ ≤ (2 / a) * (((n + 2 : Nat) : Real) /
        (xi ^ 2 + (a / 2) ^ 2)) := by
      have hscaleInv : 1 / scale ≤ 2 / a := by
        apply (div_le_div_iff₀ hspos ha).2
        linarith
      have hdenInv :
          ((n + 2 : Nat) : Real) / (xi ^ 2 + scale ^ 2) ≤
            ((n + 2 : Nat) : Real) / (xi ^ 2 + (a / 2) ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) hhalfdenpos
        nlinarith [sq_nonneg xi]
      exact mul_le_mul hscaleInv hdenInv (by positivity) (by positivity)
    _ = (2 * ((n + 2 : Nat) : Real) / a) *
        (1 / (xi ^ 2 + (a / 2) ^ 2)) := by ring

theorem density_derivative_norm_le
    (xi scale a : Real) (ha : 0 < a) (hscale : a / 2 < scale) :
    ‖((1 / scale : Real) *
        (((cayleyCoordinate scale xi + (cayleyCoordinate scale xi)⁻¹) / 2 - 1) /
          ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)))‖ ≤
      (4 / a) * (1 / (xi ^ 2 + (a / 2) ^ 2)) := by
  have hhalf : 0 < a / 2 := by positivity
  have hspos : 0 < scale := hhalf.trans hscale
  have hdenpos : 0 < xi ^ 2 + scale ^ 2 := by positivity
  have hhalfdenpos : 0 < xi ^ 2 + (a / 2) ^ 2 := by positivity
  have hz : ‖cayleyCoordinate scale xi‖ = 1 := by
    unfold cayleyCoordinate
    rw [norm_div]
    have hden : ‖(xi : Complex) - Complex.I * (scale : Complex)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hnorm :
        ‖(xi : Complex) + Complex.I * (scale : Complex)‖ =
          ‖(xi : Complex) - Complex.I * (scale : Complex)‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
    rw [hnorm, div_self hden]
  have hnum :
      ‖(cayleyCoordinate scale xi + (cayleyCoordinate scale xi)⁻¹) / 2 - 1‖ ≤ 2 := by
    calc
      ‖(cayleyCoordinate scale xi + (cayleyCoordinate scale xi)⁻¹) / 2 - 1‖ ≤
          ‖(cayleyCoordinate scale xi + (cayleyCoordinate scale xi)⁻¹) / 2‖ +
          ‖(1 : Complex)‖ := norm_sub_le _ _
      _ ≤ (‖cayleyCoordinate scale xi‖ +
          ‖(cayleyCoordinate scale xi)⁻¹‖) / ‖(2 : Complex)‖ + 1 := by
        simp only [norm_one]
        gcongr
        rw [norm_div]
        gcongr
        exact norm_add_le _ _
      _ = 2 := by rw [norm_inv, hz]; norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hspos), norm_div]
  rw [show ‖(xi : Complex) ^ 2 + (scale : Complex) ^ 2‖ =
      xi ^ 2 + scale ^ 2 by
        rw [show (xi : Complex) ^ 2 + (scale : Complex) ^ 2 =
          ((xi ^ 2 + scale ^ 2 : Real) : Complex) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]]
  calc
    1 / scale *
        (‖(cayleyCoordinate scale xi + (cayleyCoordinate scale xi)⁻¹) / 2 - 1‖ /
          (xi ^ 2 + scale ^ 2)) ≤
      1 / scale * (2 / (xi ^ 2 + scale ^ 2)) := by gcongr
    _ ≤ (2 / a) * (2 / (xi ^ 2 + (a / 2) ^ 2)) := by
      have hscaleInv : 1 / scale ≤ 2 / a := by
        apply (div_le_div_iff₀ hspos ha).2
        linarith
      have hdenInv : 2 / (xi ^ 2 + scale ^ 2) ≤
          2 / (xi ^ 2 + (a / 2) ^ 2) := by
        apply div_le_div_of_nonneg_left (by norm_num) hhalfdenpos
        nlinarith [sq_nonneg xi]
      exact mul_le_mul hscaleInv hdenInv (by positivity) (by positivity)
    _ = (4 / a) * (1 / (xi ^ 2 + (a / 2) ^ 2)) := by ring

theorem density_integral_hasDerivAt
    (source : Measure Real)
    (hIntegrable : ∀ scale : Real, 0 < scale →
      Integrable (fun xi : Real => 1 / (xi ^ 2 + scale ^ 2)) source)
    (a : Real) (ha : 0 < a) :
    HasDerivAt
      (fun scale : Real => ∫ xi : Real,
        (1 : Complex) /
          ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source)
      (∫ xi : Real, (1 / a : Real) *
        (((cayleyCoordinate a xi + (cayleyCoordinate a xi)⁻¹) / 2 - 1) /
          ((xi : Complex) ^ 2 + (a : Complex) ^ 2)) ∂source) a := by
  let domain : Set Real := Set.Ioi (a / 2)
  let bound : Real → Real := fun xi =>
    (4 / a) * (1 / (xi ^ 2 + (a / 2) ^ 2))
  let F : Real → Real → Complex := fun scale xi =>
    (1 : Complex) / ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)
  let F' : Real → Real → Complex := fun scale xi =>
    (1 / scale : Real) *
      (((cayleyCoordinate scale xi + (cayleyCoordinate scale xi)⁻¹) / 2 - 1) /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2))
  have hhalf : 0 < a / 2 := by positivity
  have hdomain : domain ∈ nhds a := by
    apply Ioi_mem_nhds
    linarith
  have hFMeasurable (scale : Real) : Measurable (F scale) := by
    dsimp only [F]
    fun_prop
  have hF'Measurable (scale : Real) : Measurable (F' scale) := by
    dsimp only [F']
    unfold cayleyCoordinate
    fun_prop
  have hFatA : Integrable (F a) source := by
    refine (hIntegrable a ha).mono' (hFMeasurable a).aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro xi
    dsimp only [F]
    have hdenpos : 0 < xi ^ 2 + a ^ 2 := by positivity
    rw [norm_div, norm_one]
    rw [show ‖(xi : Complex) ^ 2 + (a : Complex) ^ 2‖ = xi ^ 2 + a ^ 2 by
      rw [show (xi : Complex) ^ 2 + (a : Complex) ^ 2 =
        ((xi ^ 2 + a ^ 2 : Real) : Complex) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]]
  have hboundIntegrable : Integrable bound source := by
    dsimp only [bound]
    exact (hIntegrable (a / 2) hhalf).const_mul (4 / a)
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound)
    hdomain
    (by
      filter_upwards with scale
      exact (hFMeasurable scale).aestronglyMeasurable)
    hFatA
    (hF'Measurable a).aestronglyMeasurable
    (by
      apply Filter.Eventually.of_forall
      intro xi scale hscale
      dsimp only [domain] at hscale
      dsimp only [F', bound]
      exact density_derivative_norm_le xi scale a ha hscale)
    hboundIntegrable
    (by
      apply Filter.Eventually.of_forall
      intro xi scale hscale
      dsimp only [domain] at hscale
      have hspos : 0 < scale := hhalf.trans hscale
      dsimp only [F, F']
      exact density_integrand_hasDerivAt xi scale hspos)
  simpa only [F, F'] using hresult.2

theorem canonical_nat_moment_eq_source
    (source : Measure Real) (scale : Real) (hscale : 0 < scale) (n : Nat) :
    (∫ z : Complex, z ^ n ∂cayleySpectralMeasure source scale) =
      ∫ xi : Real, cayleyCoordinate scale xi ^ n /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source := by
  have hcayley : Measurable (cayleyCoordinate scale) := by
    unfold cayleyCoordinate
    fun_prop
  have hpow : AEStronglyMeasurable (fun z : Complex => z ^ n)
      (cayleySpectralMeasure source scale) := by fun_prop
  unfold cayleySpectralMeasure
  rw [MeasureTheory.integral_map hcayley.aemeasurable hpow]
  unfold resolventWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro xi
  have hdenpos : 0 < xi ^ 2 + scale ^ 2 := by positivity
  have hdenNe : (xi : Complex) ^ 2 + (scale : Complex) ^ 2 ≠ 0 := by
    exact_mod_cast hdenpos.ne'
  change (ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹)).toReal •
      cayleyCoordinate scale xi ^ n = _
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (xi ^ 2 + scale ^ 2)⁻¹)]
  rw [Complex.real_smul]
  push_cast
  field_simp [hdenNe, hdenpos.ne']

theorem canonical_inverse_moment_eq_source
    (source : Measure Real) (scale : Real) (hscale : 0 < scale) :
    (∫ z : Complex, z⁻¹ ∂cayleySpectralMeasure source scale) =
      ∫ xi : Real, (cayleyCoordinate scale xi)⁻¹ /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source := by
  have hcayley : Measurable (cayleyCoordinate scale) := by
    unfold cayleyCoordinate
    fun_prop
  have hinv : AEStronglyMeasurable (fun z : Complex => z⁻¹)
      (cayleySpectralMeasure source scale) := by fun_prop
  unfold cayleySpectralMeasure
  rw [MeasureTheory.integral_map hcayley.aemeasurable hinv]
  unfold resolventWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro xi
  have hdenpos : 0 < xi ^ 2 + scale ^ 2 := by positivity
  have hdenNe : (xi : Complex) ^ 2 + (scale : Complex) ^ 2 ≠ 0 := by
    exact_mod_cast hdenpos.ne'
  change (ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹)).toReal •
      (cayleyCoordinate scale xi)⁻¹ = _
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (xi ^ 2 + scale ^ 2)⁻¹)]
  rw [Complex.real_smul]
  push_cast
  field_simp [hdenNe, hdenpos.ne']

theorem source_inverse_first_eq_first
    (source : Measure Real)
    (hEven : Measure.map (fun xi : Real => -xi) source = source)
    (scale : Real) (hscale : 0 < scale) :
    (∫ xi : Real, (cayleyCoordinate scale xi)⁻¹ /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source) =
      ∫ xi : Real, cayleyCoordinate scale xi /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source := by
  let f : Real → Complex := fun xi => cayleyCoordinate scale xi /
    ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)
  have hf : Measurable f := by
    dsimp only [f]
    have hcoord : Measurable (cayleyCoordinate scale) := by
      unfold cayleyCoordinate
      fun_prop
    exact hcoord.div (by fun_prop)
  have hmap := MeasureTheory.integral_map (μ := source)
    (φ := fun xi : Real => -xi) (f := f) (by fun_prop)
    hf.aestronglyMeasurable
  rw [hEven] at hmap
  calc
    (∫ xi : Real, (cayleyCoordinate scale xi)⁻¹ /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source) =
      ∫ xi : Real, f (-xi) ∂source := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro xi
        dsimp only [f]
        have hplus : (xi : Complex) + Complex.I * (scale : Complex) ≠ 0 := by
          intro h
          have him := congrArg Complex.im h
          simp at him
          linarith
        have hminus : (xi : Complex) - Complex.I * (scale : Complex) ≠ 0 := by
          intro h
          have him := congrArg Complex.im h
          simp at him
          linarith
        have hnegden : ((-xi : Real) : Complex) -
            Complex.I * (scale : Complex) ≠ 0 := by
          intro h
          have him := congrArg Complex.im h
          simp at him
          linarith
        have hcayley : cayleyCoordinate scale (-xi) =
            (cayleyCoordinate scale xi)⁻¹ := by
          unfold cayleyCoordinate
          field_simp [hplus, hminus, hnegden]
          push_cast
          ring
        rw [hcayley]
        congr 1
        push_cast
        ring
    _ = ∫ xi : Real, f xi ∂source := hmap.symm
    _ = ∫ xi : Real, cayleyCoordinate scale xi /
        ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source := rfl

theorem canonical_zero_moment_eq_budget
    (source : Measure Real) (scale : Real) (hscale : 0 < scale) :
    (∫ z : Complex, z ^ (0 : Nat) ∂cayleySpectralMeasure source scale).re =
      ∫ xi : Real, 1 / (xi ^ 2 + scale ^ 2) ∂source := by
  rw [canonical_nat_moment_eq_source source scale hscale 0]
  simp only [pow_zero]
  rw [show (∫ xi : Real, (1 : Complex) /
      ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source) =
      ((∫ xi : Real, 1 / (xi ^ 2 + scale ^ 2) ∂source : Real) : Complex) by
    calc
      (∫ xi : Real, (1 : Complex) /
          ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source) =
        ∫ xi : Real, ((1 / (xi ^ 2 + scale ^ 2) : Real) : Complex) ∂source := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro xi
          have hdenpos : 0 < xi ^ 2 + scale ^ 2 := by positivity
          push_cast
          field_simp [hdenpos.ne']
      _ = _ := integral_ofReal]
  simp

theorem successor_integral_hasDerivAt
    (source : Measure Real)
    (hIntegrable : ∀ scale : Real, 0 < scale →
      Integrable (fun xi : Real => 1 / (xi ^ 2 + scale ^ 2)) source)
    (n : Nat) (a : Real) (ha : 0 < a) :
    HasDerivAt
      (fun scale : Real => ∫ xi : Real,
        cayleyCoordinate scale xi ^ (n + 1) /
          ((xi : Complex) ^ 2 + (scale : Complex) ^ 2) ∂source)
      (∫ xi : Real, (1 / a : Real) *
        ((((n + 2 : Nat) : Real) / 2 : Real) *
            cayleyCoordinate a xi ^ (n + 2) +
          ((-(n : Real)) / 2 : Real) * cayleyCoordinate a xi ^ n -
          cayleyCoordinate a xi ^ (n + 1)) /
        ((xi : Complex) ^ 2 + (a : Complex) ^ 2) ∂source) a := by
  let domain : Set Real := Set.Ioi (a / 2)
  let bound : Real → Real := fun xi =>
    (2 * ((n + 2 : Nat) : Real) / a) *
      (1 / (xi ^ 2 + (a / 2) ^ 2))
  let F : Real → Real → Complex := fun scale xi =>
    cayleyCoordinate scale xi ^ (n + 1) /
      ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)
  let F' : Real → Real → Complex := fun scale xi =>
    (1 / scale : Real) *
      ((((n + 2 : Nat) : Real) / 2 : Real) *
          cayleyCoordinate scale xi ^ (n + 2) +
        ((-(n : Real)) / 2 : Real) * cayleyCoordinate scale xi ^ n -
        cayleyCoordinate scale xi ^ (n + 1)) /
      ((xi : Complex) ^ 2 + (scale : Complex) ^ 2)
  have hhalf : 0 < a / 2 := by positivity
  have hdomain : domain ∈ nhds a := by
    apply Ioi_mem_nhds
    linarith
  have hFMeasurable (scale : Real) : Measurable (F scale) := by
    dsimp only [F]
    unfold cayleyCoordinate
    fun_prop
  have hF'Measurable (scale : Real) : Measurable (F' scale) := by
    dsimp only [F']
    unfold cayleyCoordinate
    fun_prop
  have hFatA : Integrable (F a) source := by
    refine (hIntegrable a ha).mono' (hFMeasurable a).aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro xi
    dsimp only [F]
    have hdenpos : 0 < xi ^ 2 + a ^ 2 := by positivity
    have hz : ‖cayleyCoordinate a xi‖ = 1 := by
      unfold cayleyCoordinate
      rw [norm_div]
      have hden : ‖(xi : Complex) - Complex.I * (a : Complex)‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        intro h
        have him := congrArg Complex.im h
        simp at him
        linarith
      have hnorm : ‖(xi : Complex) + Complex.I * (a : Complex)‖ =
          ‖(xi : Complex) - Complex.I * (a : Complex)‖ := by
        rw [Complex.norm_def, Complex.norm_def]
        congr 1
        simp [Complex.normSq_apply]
      rw [hnorm, div_self hden]
    rw [norm_div, norm_pow, hz, one_pow]
    rw [show ‖(xi : Complex) ^ 2 + (a : Complex) ^ 2‖ = xi ^ 2 + a ^ 2 by
      rw [show (xi : Complex) ^ 2 + (a : Complex) ^ 2 =
        ((xi ^ 2 + a ^ 2 : Real) : Complex) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]]
  have hboundIntegrable : Integrable bound source := by
    dsimp only [bound]
    exact (hIntegrable (a / 2) hhalf).const_mul
      (2 * ((n + 2 : Nat) : Real) / a)
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound)
    hdomain
    (by
      filter_upwards with scale
      exact (hFMeasurable scale).aestronglyMeasurable)
    hFatA
    (hF'Measurable a).aestronglyMeasurable
    (by
      apply Filter.Eventually.of_forall
      intro xi scale hscale
      dsimp only [domain] at hscale
      dsimp only [F', bound]
      exact successor_derivative_norm_le xi scale a n ha hscale)
    hboundIntegrable
    (by
      apply Filter.Eventually.of_forall
      intro xi scale hscale
      dsimp only [domain] at hscale
      have hspos : 0 < scale := hhalf.trans hscale
      dsimp only [F, F']
      exact successor_integrand_hasDerivAt xi scale n hspos)
  simpa only [F, F'] using hresult.2

end D5.S3.Weil.Budget.CayleyMomentTridiagonalFlowLemmas
