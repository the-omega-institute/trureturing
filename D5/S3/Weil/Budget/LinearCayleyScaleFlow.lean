/- GID: D5/S3/Weil/Budget/LinearCayleyScaleFlow
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/LinearCayleyScaleFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The logarithmic Cayley flow has the transport-decay generator and
     invariant characteristics. -/

import D5.S3.Weil.Budget.CaratheodoryScaleCovariance
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 and current-origin searches found no Cayley scale PDE, characteristic
     flow, or artanh-invariant owner.
   * Body-shape searches for the tanh disk automorphism, logarithmic scale
     flow, and the half-log disk artanh found no canonical D5 primitive.
   * Pinned Mathlib supplies differentiation under a dominated integral,
     real sinh/cosh derivatives, and complex log derivatives on the slit
     plane, but no exact logarithmic Cayley generator theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace D5.S3.Weil.Budget.LinearCayleyScaleFlow

open CaratheodoryScaleCovariance CayleyScaleChange PositiveCayleyScaleTransport

/-- The characteristic through `seed` at logarithmic time zero. -/
noncomputable def cayleyCharacteristic (seed : Complex) (tau : Real) : Complex :=
  realDiskAutomorphism (Real.tanh (-tau / 2)) seed

/-- The analytic artanh branch on the complex unit disk. -/
noncomputable def diskArtanh (w : Complex) : Complex :=
  (Complex.log (1 + w) - Complex.log (1 - w)) / 2

private theorem real_tanh_hasDerivAt (x : Real) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hquotient := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  have hvalue :
      (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
          Real.cosh x ^ 2 =
        1 - (Real.sinh x / Real.cosh x) ^ 2 := by
    field_simp [hcosh]
  rw [show Real.tanh = Real.sinh / Real.cosh by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y]
  exact hquotient.congr_deriv hvalue

private theorem disk_parameter_hasDerivAt (tau : Real) :
    HasDerivAt (fun t : Real => Real.tanh (t / 2))
      ((1 - Real.tanh (tau / 2) ^ 2) / 2) tau := by
  have hinner : HasDerivAt (fun t : Real => t / 2) (1 / 2) tau := by
    simpa using (hasDerivAt_id tau).div_const 2
  change HasDerivAt (Real.tanh ∘ fun t : Real => t / 2)
    ((1 - Real.tanh (tau / 2) ^ 2) / 2) tau
  exact ((real_tanh_hasDerivAt (tau / 2)).comp tau hinner).congr_deriv (by ring)

private theorem characteristic_parameter_hasDerivAt (tau : Real) :
    HasDerivAt (fun t : Real => Real.tanh (-t / 2))
      (-((1 - Real.tanh (-tau / 2) ^ 2) / 2)) tau := by
  have hinner : HasDerivAt (fun t : Real => -t / 2) (-1 / 2) tau := by
    simpa using (hasDerivAt_neg tau).div_const 2
  change HasDerivAt (Real.tanh ∘ fun t : Real => -t / 2)
    (-((1 - Real.tanh (-tau / 2) ^ 2) / 2)) tau
  exact ((real_tanh_hasDerivAt (-tau / 2)).comp tau hinner).congr_deriv (by ring)

private theorem cayley_coordinate_norm
    (scale spectral : Real) (hscale : 0 < scale) :
    ‖cayleyCoordinate scale spectral‖ = 1 := by
  have hden : (spectral : Complex) - Complex.I * (scale : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  unfold cayleyCoordinate
  rw [norm_div]
  have hnorm :
      ‖(spectral : Complex) + Complex.I * (scale : Complex)‖ =
        ‖(spectral : Complex) - Complex.I * (scale : Complex)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  rw [hnorm, div_self]
  simpa using hden

private theorem kernel_den_ne
    (z w : Complex) (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) : z - w ≠ 0 := by
  intro h
  have hzw : z = w := sub_eq_zero.mp h
  rw [hzw] at hz
  linarith

private theorem kernel_norm_le
    (z w : Complex) (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) :
    ‖caratheodoryKernel z w‖ ≤ (1 + ‖w‖) / (1 - ‖w‖) := by
  have hnum : ‖z + w‖ ≤ 1 + ‖w‖ := by
    simpa only [hz] using norm_add_le z w
  have hden : 1 - ‖w‖ ≤ ‖z - w‖ := by
    simpa only [hz] using norm_sub_norm_le z w
  have hpos : 0 < 1 - ‖w‖ := sub_pos.mpr hw
  unfold caratheodoryKernel
  rw [norm_div]
  exact div_le_div₀ (by positivity) hnum hpos hden

private theorem kernel_hasDerivAt
    (z w : Complex) (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) :
    HasDerivAt (caratheodoryKernel z) (2 * z / (z - w) ^ 2) w := by
  have hden := kernel_den_ne z w hz hw
  have hnum := (hasDerivAt_const w z).add (hasDerivAt_id w)
  have hdenom := (hasDerivAt_const w z).sub (hasDerivAt_id w)
  have hquotient := hnum.div hdenom hden
  simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, zero_sub, one_mul] at hquotient
  change HasDerivAt (fun x : Complex => (z + x) / (z - x))
    (2 * z / (z - w) ^ 2) w
  exact hquotient.congr_deriv (by
    field_simp [hden]
    ring)

private theorem caratheodory_spatial_hasDerivAt
    (source : Measure Real) (scale : Real) (hscale : 0 < scale)
    [IsFiniteMeasure (resolventWeightedMeasure source scale)]
    (w : Complex) (hw : ‖w‖ < 1) :
    HasDerivAt (caratheodoryFunction source scale)
      (∫ spectral, 2 * cayleyCoordinate scale spectral /
        (cayleyCoordinate scale spectral - w) ^ 2
        ∂resolventWeightedMeasure source scale) w := by
  let radius : Real := (1 + ‖w‖) / 2
  let margin : Real := (1 - ‖w‖) / 2
  let domain : Set Complex := Metric.ball 0 radius
  let derivative : Complex → Real → Complex := fun x spectral =>
    2 * cayleyCoordinate scale spectral /
      (cayleyCoordinate scale spectral - x) ^ 2
  have hcayley : Measurable (cayleyCoordinate scale) := by
    unfold cayleyCoordinate
    fun_prop
  have hkernel (x : Complex) : Measurable
      (fun spectral => caratheodoryKernel (cayleyCoordinate scale spectral) x) := by
    unfold caratheodoryKernel
    fun_prop
  have hkernelTarget (x : Complex) : Measurable
      (fun z : Complex => caratheodoryKernel z x) := by
    unfold caratheodoryKernel
    fun_prop
  have hderivative (x : Complex) : Measurable (derivative x) := by
    dsimp only [derivative]
    fun_prop
  have hradius : ‖w‖ < radius := by
    dsimp only [radius]
    linarith
  have hmargin : 0 < margin := by
    dsimp only [margin]
    linarith
  have hdomain : domain ∈ nhds w := by
    apply Metric.isOpen_ball.mem_nhds
    simpa only [domain, Metric.mem_ball, dist_zero_right] using hradius
  have hintegrable : Integrable
      (fun spectral => caratheodoryKernel (cayleyCoordinate scale spectral) w)
      (resolventWeightedMeasure source scale) := by
    apply Integrable.of_bound (hkernel w).aestronglyMeasurable
      ((1 + ‖w‖) / (1 - ‖w‖))
    apply Filter.Eventually.of_forall
    intro spectral
    exact kernel_norm_le _ _ (cayley_coordinate_norm scale spectral hscale) hw
  have hbound : ∀ᵐ spectral ∂resolventWeightedMeasure source scale,
      ∀ x ∈ domain, ‖derivative x spectral‖ ≤ 2 / margin ^ 2 := by
    apply Filter.Eventually.of_forall
    intro spectral x hx
    have hz := cayley_coordinate_norm scale spectral hscale
    have hxnorm : ‖x‖ < radius := by
      simpa only [domain, Metric.mem_ball, dist_zero_right] using hx
    have hden : margin ≤ ‖cayleyCoordinate scale spectral - x‖ := by
      have hreverse := norm_sub_norm_le (cayleyCoordinate scale spectral) x
      rw [hz] at hreverse
      dsimp only [radius, margin] at hxnorm ⊢
      linarith
    have hdenNonneg : 0 ≤ ‖cayleyCoordinate scale spectral - x‖ := norm_nonneg _
    have hsquare : margin ^ 2 ≤ ‖cayleyCoordinate scale spectral - x‖ ^ 2 := by
      nlinarith
    have htwo : ‖(2 : Complex)‖ = 2 := by norm_num
    dsimp only [derivative]
    rw [norm_div, norm_mul, htwo, hz, mul_one, norm_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hmargin) hsquare
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x spectral =>
      caratheodoryKernel (cayleyCoordinate scale spectral) x)
    (F' := derivative) (bound := fun _ => 2 / margin ^ 2)
    hdomain
    (by filter_upwards with x using (hkernel x).aestronglyMeasurable)
    hintegrable
    (hderivative w).aestronglyMeasurable
    hbound
    (integrable_const _)
    (by
      apply Filter.Eventually.of_forall
      intro spectral x hx
      have hxnorm : ‖x‖ < radius := by
        simpa only [domain, Metric.mem_ball, dist_zero_right] using hx
      have hxunit : ‖x‖ < 1 := by
        dsimp only [radius] at hxnorm
        linarith
      exact kernel_hasDerivAt _ _
        (cayley_coordinate_norm scale spectral hscale) hxunit)
  have hmap : caratheodoryFunction source scale = fun x =>
      ∫ spectral, caratheodoryKernel (cayleyCoordinate scale spectral) x
        ∂resolventWeightedMeasure source scale := by
    funext x
    unfold caratheodoryFunction cayleySpectralMeasure
    rw [MeasureTheory.integral_map hcayley.aemeasurable
      (hkernelTarget x).aestronglyMeasurable]
  rw [hmap]
  exact hresult.2

private theorem automorphism_den_ne
    (r : Real) (w : Complex) (hr : |r| < 1) (hw : ‖w‖ < 1) :
    1 + (r : Complex) * w ≠ 0 := by
  intro h
  have hmul : (r : Complex) * w = -1 := by
    linear_combination h
  have hnorm := congrArg norm hmul
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg, norm_one] at hnorm
  have hproduct : |r| * ‖w‖ < 1 := by
    nlinarith [abs_nonneg r, norm_nonneg w]
  linarith

private theorem automorphism_mem_unit
    (r : Real) (w : Complex) (hr : |r| < 1) (hw : ‖w‖ < 1) :
    ‖realDiskAutomorphism r w‖ < 1 := by
  have hrsq : r ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one r).2 hr
  have hwsq : Complex.normSq w < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg w]
  simp only [Complex.normSq_apply] at hwsq
  have hnormSq :
      Complex.normSq (w + (r : Complex)) <
        Complex.normSq (1 + (r : Complex) * w) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  have hdenpos : 0 < ‖1 + (r : Complex) * w‖ := by
    have : 0 < Complex.normSq (1 + (r : Complex) * w) :=
      lt_of_le_of_lt (Complex.normSq_nonneg _) hnormSq
    rw [← Complex.sq_norm] at this
    nlinarith [norm_nonneg (1 + (r : Complex) * w)]
  unfold realDiskAutomorphism
  rw [norm_div, div_lt_one hdenpos]
  nlinarith [Complex.sq_norm (w + (r : Complex)),
    Complex.sq_norm (1 + (r : Complex) * w), norm_nonneg (w + (r : Complex)),
    norm_nonneg (1 + (r : Complex) * w)]

private theorem automorphism_parameter_hasDerivAt
    (r : Real) (w : Complex) (hden : 1 + (r : Complex) * w ≠ 0) :
    HasDerivAt (fun s : Real => realDiskAutomorphism s w)
      ((1 - w ^ 2) / (1 + (r : Complex) * w) ^ 2) r := by
  have hcast : HasDerivAt (fun s : Real => (s : Complex)) 1 r :=
    Complex.ofRealCLM.hasDerivAt
  have hnum : HasDerivAt (fun s : Real => w + (s : Complex)) 1 r :=
    hcast.const_add w
  have hdenom : HasDerivAt (fun s : Real => 1 + (s : Complex) * w) w r :=
    ((hcast.mul_const w).const_add 1).congr_deriv (by simp)
  unfold realDiskAutomorphism
  exact (hnum.div hdenom hden).congr_deriv (by
    field_simp [hden]
    ring)

private theorem automorphism_generator_identity
    (r : Real) (w : Complex) (hden : 1 + (r : Complex) * w ≠ 0) :
    (1 - w ^ 2) * (1 - (r : Complex) ^ 2) /
          (1 + (r : Complex) * w) ^ 2 =
      1 - realDiskAutomorphism r w ^ 2 := by
  unfold realDiskAutomorphism
  rw [div_pow]
  have hdenSquare : (1 + (r : Complex) * w) ^ 2 ≠ 0 := pow_ne_zero 2 hden
  rw [div_eq_iff hdenSquare]
  conv_rhs =>
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hdenSquare]
  ring

private theorem flow_at_zero_hasDerivAt
    (profile : Complex → Complex) (profileDerivative : Complex)
    (w : Complex) (hprofile : HasDerivAt profile profileDerivative w) :
    HasDerivAt (fun h : Real =>
        (Real.exp (-h) : Complex) *
          profile (realDiskAutomorphism (Real.tanh (h / 2)) w))
      (((1 - w ^ 2) / 2) * profileDerivative - profile w) 0 := by
  have hparameter := disk_parameter_hasDerivAt 0
  have hautoParameter := automorphism_parameter_hasDerivAt 0 w (by simp)
  have hautoTime : HasDerivAt (fun h : Real =>
      realDiskAutomorphism (Real.tanh (h / 2)) w) ((1 - w ^ 2) / 2) 0 := by
    change HasDerivAt
      ((fun s : Real => realDiskAutomorphism s w) ∘ fun h : Real =>
        Real.tanh (h / 2)) ((1 - w ^ 2) / 2) 0
    have hautoAt : HasDerivAt (fun s : Real => realDiskAutomorphism s w)
        ((1 - w ^ 2) / (1 + (Real.tanh (0 / 2) : Complex) * w) ^ 2)
        (Real.tanh (0 / 2)) := by simpa using hautoParameter
    exact (hautoAt.scomp 0 hparameter).congr_deriv (by
      push_cast
      norm_num only [zero_div]
      rw [Real.tanh_zero, Complex.tanh_zero]
      norm_num
      ring)
  have hprofilePath : HasDerivAt (fun h : Real =>
      profile (realDiskAutomorphism (Real.tanh (h / 2)) w))
      (((1 - w ^ 2) / 2) * profileDerivative) 0 := by
    change HasDerivAt
      (profile ∘ fun h : Real => realDiskAutomorphism (Real.tanh (h / 2)) w)
      (((1 - w ^ 2) / 2) * profileDerivative) 0
    exact (hprofile.scomp_of_eq 0 hautoTime (by simp [realDiskAutomorphism])).congr_deriv
      (by simp only [smul_eq_mul])
  have hexpReal : HasDerivAt (fun h : Real => Real.exp (-h)) (-1) 0 := by
    change HasDerivAt (Real.exp ∘ fun h : Real => -h) (-1) 0
    exact ((Real.hasDerivAt_exp 0).comp_of_eq 0 (hasDerivAt_neg 0) (by simp)).congr_deriv
      (by simp)
  have hexp : HasDerivAt (fun h : Real => (Real.exp (-h) : Complex)) (-1) 0 := by
    have hcast : HasDerivAt (fun x : Real => (x : Complex)) 1 (Real.exp (-0)) :=
      Complex.ofRealCLM.hasDerivAt
    change HasDerivAt
      ((fun x : Real => (x : Complex)) ∘ fun h : Real => Real.exp (-h)) (-1) 0
    exact (hcast.scomp 0 hexpReal).congr_deriv (by
      change ((-1 : Real) : Complex) * 1 = -1
      norm_num)
  exact (hexp.mul hprofilePath).congr_deriv (by
    simp [realDiskAutomorphism]
    ring)

private theorem observer_parameter_exp (tau h : Real) :
    observerScaleParameter (Real.exp tau) (Real.exp (tau + h)) =
      Real.tanh (h / 2) := by
  rw [Real.tanh_eq]
  unfold observerScaleParameter
  rw [Real.exp_add]
  field_simp [Real.exp_ne_zero]
  have heq : Real.exp h * Real.exp (-h / 2) = Real.exp (h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp h - 1) * (Real.exp (h / 2) + Real.exp (-(h / 2))) =
        (1 + Real.exp h) * (Real.exp (h / 2) - Real.exp (-(h / 2))) +
          2 * (Real.exp h * Real.exp (-h / 2) - Real.exp (h / 2)) := by ring
    _ = (1 + Real.exp h) *
        (Real.exp (h / 2) - Real.exp (-(h / 2))) := by rw [heq]; ring

private theorem exp_scale_ratio (tau h : Real) :
    Real.exp tau / Real.exp (tau + h) = Real.exp (-h) := by
  rw [Real.exp_add]
  field_simp [Real.exp_ne_zero]
  rw [← Real.exp_add]
  rw [show h + -h = 0 by ring, Real.exp_zero]

private theorem scale_flow_identity
    (source : Measure Real)
    (hEven : Measure.map (fun x : Real => -x) source = source)
    (hFinite : ∀ scale : Real, 0 < scale →
      IsFiniteMeasure (resolventWeightedMeasure source scale))
    (tau h : Real) (w : Complex) (hw : ‖w‖ < 1) :
    caratheodoryFunction source (Real.exp (tau + h)) w =
      (Real.exp (-h) : Complex) *
        caratheodoryFunction source (Real.exp tau)
          (realDiskAutomorphism (Real.tanh (h / 2)) w) := by
  letI : IsFiniteMeasure (resolventWeightedMeasure source (Real.exp tau)) :=
    hFinite _ (Real.exp_pos tau)
  letI : IsFiniteMeasure
      (resolventWeightedMeasure source (Real.exp (tau + h))) :=
    hFinite _ (Real.exp_pos (tau + h))
  have hcovariance := (caratheodory_scale_covariance source
    (Real.exp tau) (Real.exp (tau + h)) (Real.exp_pos tau)
    (Real.exp_pos (tau + h)) hEven w hw).1
  rw [observer_parameter_exp] at hcovariance
  rw [exp_scale_ratio] at hcovariance
  exact hcovariance

private theorem canonical_flow_hasDerivAt
    (source : Measure Real)
    (hEven : Measure.map (fun x : Real => -x) source = source)
    (hFinite : ∀ scale : Real, 0 < scale →
      IsFiniteMeasure (resolventWeightedMeasure source scale))
    (tau : Real) (w : Complex) (hw : ‖w‖ < 1) :
    HasDerivAt (fun t : Real =>
        caratheodoryFunction source (Real.exp t) w)
      (((1 - w ^ 2) / 2) *
          deriv (caratheodoryFunction source (Real.exp tau)) w -
        caratheodoryFunction source (Real.exp tau) w) tau := by
  letI : IsFiniteMeasure (resolventWeightedMeasure source (Real.exp tau)) :=
    hFinite _ (Real.exp_pos tau)
  have hspatial := caratheodory_spatial_hasDerivAt source (Real.exp tau)
    (Real.exp_pos tau) w hw
  have hzero := flow_at_zero_hasDerivAt
    (caratheodoryFunction source (Real.exp tau))
    (deriv (caratheodoryFunction source (Real.exp tau)) w) w
    (hspatial.congr_deriv hspatial.deriv.symm)
  have hcanonical : HasDerivAt (fun h : Real =>
      caratheodoryFunction source (Real.exp (tau + h)) w)
      (((1 - w ^ 2) / 2) *
          deriv (caratheodoryFunction source (Real.exp tau)) w -
        caratheodoryFunction source (Real.exp tau) w) 0 := by
    convert hzero using 1
    funext h
    exact scale_flow_identity source hEven hFinite tau h w hw
  have hshift : HasDerivAt (fun t : Real => t - tau) 1 tau := by
    simpa using (hasDerivAt_id tau).sub_const tau
  have hcomp : HasDerivAt
      ((fun h : Real => caratheodoryFunction source (Real.exp (tau + h)) w) ∘
        fun t : Real => t - tau)
      (((1 - w ^ 2) / 2) *
          deriv (caratheodoryFunction source (Real.exp tau)) w -
        caratheodoryFunction source (Real.exp tau) w) tau := by
    exact (hcanonical.scomp_of_eq tau hshift (by simp)).congr_deriv (by simp)
  apply hcomp.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  simp only [Function.comp_apply]
  congr 3
  ring

private theorem characteristic_hasDerivAt
    (seed : Complex) (tau : Real) (hseed : ‖seed‖ < 1) :
    HasDerivAt (cayleyCharacteristic seed)
      (-((1 - cayleyCharacteristic seed tau ^ 2) / 2)) tau := by
  let r := Real.tanh (-tau / 2)
  have hr : |r| < 1 := by
    dsimp only [r]
    exact Real.abs_tanh_lt_one _
  have hden := automorphism_den_ne r seed hr hseed
  have hparameter := characteristic_parameter_hasDerivAt tau
  have hautoParameter := automorphism_parameter_hasDerivAt r seed hden
  dsimp only [r] at hautoParameter
  have hcomp := hautoParameter.scomp tau hparameter
  have hgenerator := automorphism_generator_identity
    (Real.tanh (-tau / 2)) seed hden
  push_cast at hgenerator
  have hderiv :
      (-((1 - Real.tanh (-tau / 2) ^ 2) / 2)) •
          ((1 - seed ^ 2) /
            (1 + (Real.tanh (-tau / 2) : Complex) * seed) ^ 2) =
        -((1 - realDiskAutomorphism (Real.tanh (-tau / 2)) seed ^ 2) / 2) := by
    rw [Complex.real_smul]
    push_cast
    calc
      -((1 - Complex.tanh (-(tau : Complex) / 2) ^ 2) / 2) *
          ((1 - seed ^ 2) /
            (1 + Complex.tanh (-(tau : Complex) / 2) * seed) ^ 2) =
          -(((1 - seed ^ 2) *
            (1 - Complex.tanh (-(tau : Complex) / 2) ^ 2) /
              (1 + Complex.tanh (-(tau : Complex) / 2) * seed) ^ 2) / 2) := by ring
      _ = -((1 - realDiskAutomorphism (Real.tanh (-tau / 2)) seed ^ 2) / 2) := by
        rw [hgenerator]
  unfold cayleyCharacteristic
  dsimp only [r] at *
  change HasDerivAt
    ((fun s : Real => realDiskAutomorphism s seed) ∘
      fun t : Real => Real.tanh (-t / 2)) _ tau
  exact hcomp.congr_deriv hderiv

private theorem characteristic_mem_unit
    (seed : Complex) (tau : Real) (hseed : ‖seed‖ < 1) :
    ‖cayleyCharacteristic seed tau‖ < 1 := by
  unfold cayleyCharacteristic
  exact automorphism_mem_unit _ seed (Real.abs_tanh_lt_one _) hseed

private theorem diskArtanh_hasDerivAt
    (w : Complex) (hw : ‖w‖ < 1) :
    HasDerivAt diskArtanh (1 / (1 - w ^ 2)) w := by
  have hplus : 1 + w ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one hw
  have hminus : 1 - w ∈ Complex.slitPlane := by
    have hneg : ‖-w‖ < 1 := by simpa only [norm_neg] using hw
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hneg
  have hplusDeriv :
      HasDerivAt (fun z : Complex => Complex.log (1 + z)) (1 / (1 + w)) w := by
    change HasDerivAt (Complex.log ∘ fun z : Complex => 1 + z) (1 / (1 + w)) w
    exact ((Complex.hasDerivAt_log hplus).comp w
      ((hasDerivAt_const w 1).add (hasDerivAt_id w))).congr_deriv (by ring)
  have hminusDeriv :
      HasDerivAt (fun z : Complex => Complex.log (1 - z)) (-1 / (1 - w)) w := by
    change HasDerivAt (Complex.log ∘ fun z : Complex => 1 - z) (-1 / (1 - w)) w
    exact ((Complex.hasDerivAt_log hminus).comp w
      ((hasDerivAt_const w 1).sub (hasDerivAt_id w))).congr_deriv (by ring)
  have hplusNe := Complex.slitPlane_ne_zero hplus
  have hminusNe := Complex.slitPlane_ne_zero hminus
  have hsquareNe : 1 - w ^ 2 ≠ 0 := by
    rw [show 1 - w ^ 2 = (1 - w) * (1 + w) by ring]
    exact mul_ne_zero hminusNe hplusNe
  unfold diskArtanh
  exact ((hplusDeriv.sub hminusDeriv).div_const 2).congr_deriv (by
    field_simp [hplusNe, hminusNe, hsquareNe]
    ring)

/-- The canonical logarithmic Caratheodory flow satisfies the linear PDE; its
explicit characteristic satisfies the characteristic ODE, and the disk
artanh coordinate plus half the logarithmic time is invariant. -/
theorem linear_cayley_scale_pde
    (source : Measure Real)
    (hEven : Measure.map (fun x : Real => -x) source = source)
    (hFinite : ∀ scale : Real, 0 < scale →
      IsFiniteMeasure (resolventWeightedMeasure source scale))
    (tau : Real) (w seed : Complex) (hw : ‖w‖ < 1) (hseed : ‖seed‖ < 1) :
    HasDerivAt (fun t : Real =>
        caratheodoryFunction source (Real.exp t) w)
        (((1 - w ^ 2) / 2) *
            deriv (caratheodoryFunction source (Real.exp tau)) w -
          caratheodoryFunction source (Real.exp tau) w) tau ∧
      HasDerivAt (cayleyCharacteristic seed)
        (-((1 - cayleyCharacteristic seed tau ^ 2) / 2)) tau ∧
      HasDerivAt (fun t : Real =>
          diskArtanh (cayleyCharacteristic seed t) + (t : Complex) / 2)
        0 tau := by
  have hflow := canonical_flow_hasDerivAt source hEven hFinite tau w hw
  have hcharacteristic := characteristic_hasDerivAt seed tau hseed
  have hcharacteristicUnit := characteristic_mem_unit seed tau hseed
  have hartanh := diskArtanh_hasDerivAt
    (cayleyCharacteristic seed tau) hcharacteristicUnit
  have hcomposition : HasDerivAt (fun t : Real =>
      diskArtanh (cayleyCharacteristic seed t)) (-1 / 2 : Complex) tau := by
    have hcomp := HasDerivAt.scomp tau hartanh hcharacteristic
    have hnonzero : 1 - cayleyCharacteristic seed tau ^ 2 ≠ 0 := by
      intro h
      have hsquare : cayleyCharacteristic seed tau ^ 2 = 1 := (sub_eq_zero.mp h).symm
      have hnorm := congrArg norm hsquare
      rw [norm_pow, norm_one] at hnorm
      nlinarith [norm_nonneg (cayleyCharacteristic seed tau)]
    change HasDerivAt (diskArtanh ∘ cayleyCharacteristic seed)
      (-1 / 2 : Complex) tau
    apply hcomp.congr_deriv
    simp only [smul_eq_mul]
    calc
      -((1 - cayleyCharacteristic seed tau ^ 2) / 2) *
          (1 / (1 - cayleyCharacteristic seed tau ^ 2)) =
          -(((1 - cayleyCharacteristic seed tau ^ 2) *
            (1 - cayleyCharacteristic seed tau ^ 2)⁻¹) / 2) := by ring
      _ = -(1 / 2) := by rw [mul_inv_cancel₀ hnonzero]
      _ = -1 / 2 := by ring
  have htime : HasDerivAt (fun t : Real => (t : Complex) / 2) (1 / 2) tau := by
    simpa using Complex.ofRealCLM.hasDerivAt.div_const 2
  exact ⟨hflow, hcharacteristic,
    (hcomposition.add htime).congr_deriv (by ring)⟩

#print axioms linear_cayley_scale_pde

end D5.S3.Weil.Budget.LinearCayleyScaleFlow
