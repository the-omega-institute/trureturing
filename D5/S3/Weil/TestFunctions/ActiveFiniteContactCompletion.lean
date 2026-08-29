/- GID: D5/S3/Weil/TestFunctions/ActiveFiniteContactCompletion
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/ActiveFiniteContactCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct active finite-contact circle completions with exact observer moments. -/

import D5.S3.Weil.TestFunctions.CayleyMomentTransport
import D5.S3.Fourier.FourierLaplaceEntire
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support

/- Library-search audit trail (2026-08-29):
   * D5 has the canonical Cayley moment function, normalized circle Haar
     measure, Weil test-function carrier, and entire Fourier-Laplace transform;
     this module imports those owners rather than redeclaring them.
   * D5 body-shape searches found no active-contact finiteness or finite
     positive cubature owner. Pinned Mathlib supplies isolated-zero analysis,
     convex-hull Caratheodory reduction, and finite-support measure identities,
     but no packaged theorem on this source carrier.
   * The local proof confines active real zeros by Schwartz decay, applies
     analytic uniqueness, and then proves the positive cubature bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.CayleyMomentTransport
open D5.S3.Weil.Budget.FullCirclePrimalAttainment

namespace D5.S3.Weil.TestFunctions.ActiveFiniteContactCompletion

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

private theorem analytic_real_active_function
    (a theta : Real) (phi : WeilTestFunction) :
    AnalyticOnNhd Real
      (fun xi : Real => (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
        fourierLaplace phi xi + theta)) univ := by
  intro xi _
  have hfourier : AnalyticAt Complex (fourierLaplace phi) (xi : Complex) :=
    (fourierLaplace_entire phi).analyticAt _
  have hcomplex : AnalyticAt Complex
      (fun z : Complex => (z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z + theta)
      (xi : Complex) := by
    fun_prop
  exact hcomplex.restrictScalars.comp (Complex.ofRealCLM.analyticAt xi)

private theorem active_real_zero_set_finite
    (a theta : Real) (htheta : 0 < theta) (phi : WeilTestFunction) :
    {xi : Real | (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
      fourierLaplace phi xi + theta) = 0}.Finite := by
  let schwartz : SchwartzMap Real Complex :=
    phi.hasCompactSupport.toSchwartzMap phi.contDiff
  let c : Real := 2 * Real.pi
  let bound : Real := SchwartzMap.seminorm Real 3 0 (FourierTransform.fourier schwartz)
  let radius : Real := max 1 (max (abs a) (2 * (bound + 1) * c ^ 3 / theta))
  let zeros : Set Real := {xi : Real | (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
    fourierLaplace phi xi + theta) = 0}
  have hconfined : zeros ⊆ Set.Icc (-radius) radius := by
    intro xi hxi
    by_contra hout
    have habs : radius < |xi| := by
      apply lt_of_not_ge
      intro habs
      apply hout
      exact ⟨(abs_le.mp habs).1, (abs_le.mp habs).2⟩
    have hxi1 : 1 < |xi| := lt_of_le_of_lt (le_max_left _ _) habs
    have hxia : |a| < |xi| := lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_max_right 1 _)) habs
    have hboundRadius : 2 * (bound + 1) * c ^ 3 / theta < |xi| :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) habs
    have hseminorm := SchwartzMap.norm_pow_mul_le_seminorm Real
      (FourierTransform.fourier schwartz) 3 (c⁻¹ * xi)
    have hfourier : fourierLaplace phi xi =
        (FourierTransform.fourier schwartz) (c⁻¹ * xi) := by
      rw [fourierLaplace_real_eq_fourier]
      rw [show mathlibFrequency xi = c⁻¹ * xi by
        unfold mathlibFrequency c
        ring]
      exact congrFun (SchwartzMap.fourier_coe schwartz).symm _
    -- The remaining estimate is purely algebraic: fourth-order Schwartz decay makes
    -- the quadratic Fourier multiplier smaller than the positive active pressure.
    have hsmall :
        ‖((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
          fourierLaplace phi xi‖ < theta := by
      have hc : 0 < c := by
        dsimp [c]
        positivity
      have hb : 0 ≤ bound := by
        dsimp [bound]
        positivity
      have hfreqabs : |c⁻¹ * xi| = |xi| / c := by
        rw [abs_mul, abs_inv, abs_of_pos hc]
        simp only [div_eq_mul_inv]
        ring
      have hscaled : |xi| ^ 3 * ‖(FourierTransform.fourier schwartz) (c⁻¹ * xi)‖ ≤
          bound * c ^ 3 := by
        rw [Real.norm_eq_abs, hfreqabs] at hseminorm
        calc
          |xi| ^ 3 * ‖(FourierTransform.fourier schwartz) (c⁻¹ * xi)‖ =
              c ^ 3 * ((|xi| / c) ^ 3 *
                ‖(FourierTransform.fourier schwartz) (c⁻¹ * xi)‖) := by
                field_simp [hc.ne']
          _ ≤ c ^ 3 * bound := mul_le_mul_of_nonneg_left hseminorm (by positivity)
          _ = bound * c ^ 3 := by ring
      have hpoly : ‖(xi : Complex) ^ 2 + (a : Complex) ^ 2‖ ≤ 2 * |xi| ^ 2 := by
        calc
          ‖(xi : Complex) ^ 2 + (a : Complex) ^ 2‖ ≤
              ‖(xi : Complex) ^ 2‖ + ‖(a : Complex) ^ 2‖ := norm_add_le _ _
          _ = |xi| ^ 2 + |a| ^ 2 := by simp [norm_pow, Real.norm_eq_abs]
          _ ≤ 2 * |xi| ^ 2 := by
            have hsquares : |a| ^ 2 ≤ |xi| ^ 2 :=
              (sq_le_sq₀ (abs_nonneg a) (abs_nonneg xi)).2 hxia.le
            linarith
      have hproduct :
          ‖((xi : Complex) ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi xi‖ ≤
            2 * |xi| ^ 2 * ‖(FourierTransform.fourier schwartz) (c⁻¹ * xi)‖ := by
        rw [norm_mul, hfourier]
        exact mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      have hpressure : 2 * bound * c ^ 3 < theta * |xi| := by
        have hstrict : 2 * bound * c ^ 3 < 2 * (bound + 1) * c ^ 3 := by
          nlinarith [pow_pos hc 3]
        exact hstrict.trans (by
          simpa [mul_comm] using (div_lt_iff₀ htheta).mp hboundRadius)
      refine lt_of_le_of_lt hproduct ?_
      have hmul :
          (2 * |xi| ^ 2 * ‖(FourierTransform.fourier schwartz) (c⁻¹ * xi)‖) * |xi| <
            theta * |xi| := by
        calc
          (2 * |xi| ^ 2 * ‖(FourierTransform.fourier schwartz) (c⁻¹ * xi)‖) * |xi| =
              2 * (|xi| ^ 3 * ‖(FourierTransform.fourier schwartz) (c⁻¹ * xi)‖) := by ring
          _ ≤ 2 * (bound * c ^ 3) := by nlinarith
          _ < theta * |xi| := by nlinarith
      exact lt_of_mul_lt_mul_right hmul (show 0 ≤ |xi| by positivity)
    have : ‖((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
        fourierLaplace phi xi‖ = theta := by
      change ((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
        fourierLaplace phi xi + theta = 0 at hxi
      rw [← neg_eq_iff_add_eq_zero] at hxi
      calc
        ‖((xi : Complex) ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi xi‖ =
            ‖-(((xi : Complex) ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi xi)‖ :=
              (norm_neg _).symm
        _ = ‖(theta : Complex)‖ := congrArg norm hxi
        _ = theta := by simp [htheta.le]
    linarith
  by_contra hinfinite
  have hzerosInfinite : zeros.Infinite := hinfinite
  obtain ⟨xi, hxiIcc, hacc⟩ :=
    hzerosInfinite.exists_accPt_of_subset_isCompact isCompact_Icc hconfined
  have hzeroFrequently :
      ∃ᶠ y : Real in 𝓝[≠] xi, (((y : Complex) ^ 2 + (a : Complex) ^ 2) *
        fourierLaplace phi y + theta) = 0 := by
    exact (accPt_iff_frequently_nhdsNE.mp hacc).mono fun y hy => hy
  have hidentical := (analytic_real_active_function a theta phi).eq_of_frequently_eq
    analyticOnNhd_const hzeroFrequently
  have houtside : radius + 1 ∉ Set.Icc (-radius) radius := by
    simp
  have hnotzero : radius + 1 ∉ zeros := fun hz => houtside (hconfined hz)
  apply hnotzero
  simpa only [zeros, Set.mem_setOf_eq] using congrFun hidentical (radius + 1)

private theorem cayley_circle_inverse
    (a : Real) (ha : 0 < a) (z : Circle) (hz : z ≠ 1) :
    cayleyCircle a ha (cayleyInverse a z) = z := by
  let w : Complex := (z : Complex)
  let t : Complex := Complex.I * a * (w + 1) / (w - 1)
  have hwne : w - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hz (Circle.ext h)
  have hunit : w.re ^ 2 + w.im ^ 2 = 1 := by
    simpa [w, Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  have htim : t.im = 0 := by
    dsimp only [t]
    rw [Complex.div_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, zero_mul, one_mul, zero_add, sub_zero]
    norm_num
    have hnorm : Complex.normSq (w - 1) ≠ 0 :=
      ne_of_gt (Complex.normSq_pos.mpr hwne)
    field_simp [hnorm]
    nlinarith
  have htreal : ((t.re : Real) : Complex) = t := by
    apply Complex.ext
    · simp
    · simp [htim]
  apply Circle.ext
  change cayleyCharacter a (cayleyInverse a z) = w
  rw [cayleyInverse]
  change cayleyCharacter a t.re = w
  rw [cayleyCharacter]
  rw [htreal]
  have htden : t - Complex.I * a ≠ 0 := by
    intro hzero
    have hmul := congrArg (fun u : Complex => u * (w - 1)) hzero
    dsimp only [t] at hmul
    field_simp [hwne] at hmul
    apply ha.ne'
    exact_mod_cast (by
      have hi : (2 : Complex) * Complex.I * a = 0 := by
        linear_combination hmul
      simpa using hi)
  apply (div_eq_iff htden).2
  dsimp only [t]
  field_simp [hwne]
  ring

private theorem cayley_circle_neg
    (a : Real) (ha : 0 < a) (xi : Real) :
    cayleyCircle a ha (-xi) = (cayleyCircle a ha xi)⁻¹ := by
  apply Circle.ext
  change cayleyCharacter a (-xi) = (cayleyCharacter a xi)⁻¹
  rw [cayleyCharacter, cayleyCharacter]
  have hplus : ((xi : Complex) + Complex.I * a) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_add, one_mul] at him
    norm_num at him
    linarith
  rw [inv_div]
  push_cast
  rw [show -(xi : Complex) + Complex.I * a =
      -((xi : Complex) - Complex.I * a) by ring]
  rw [show -(xi : Complex) - Complex.I * a =
      -((xi : Complex) + Complex.I * a) by ring]
  apply (div_eq_div_iff (neg_ne_zero.mpr hplus) hplus).2
  ring

private theorem cayley_circle_ne_one
    (a : Real) (ha : 0 < a) (xi : Real) :
    cayleyCircle a ha xi ≠ 1 := by
  intro h
  have hcomplex : cayleyCharacter a xi = (1 : Complex) := congrArg Subtype.val h
  rw [cayleyCharacter, div_eq_one_iff_eq] at hcomplex
  · have him := congrArg Complex.im hcomplex
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_add, one_mul, Complex.sub_im,
      zero_sub] at him
    norm_num at him
    linarith
  · intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_sub, one_mul] at him
    norm_num at him
    linarith

private theorem cayley_inverse_circle
    (a : Real) (ha : 0 < a) (xi : Real) :
    cayleyInverse a (cayleyCircle a ha xi) = xi := by
  rw [cayleyInverse]
  change
    (Complex.I * a * (cayleyCharacter a xi + 1) /
      (cayleyCharacter a xi - 1)).re = xi
  have hden : ((xi : Complex) - Complex.I * a) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_sub, one_mul] at him
    norm_num at him
    linarith
  have hcomplex :
      Complex.I * a * (cayleyCharacter a xi + 1) /
          (cayleyCharacter a xi - 1) =
        (xi : Complex) := by
    rw [cayleyCharacter]
    field_simp [hden]
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

private theorem fourier_laplace_neg
    (phi : WeilTestFunction) (xi : Real) :
    fourierLaplace phi (-xi) = fourierLaplace phi xi := by
  rw [fourierLaplace_apply, fourierLaplace_apply]
  rw [← integral_neg_eq_self
    (fun x : Real => Complex.exp (-Complex.I * (-xi : Complex) * (x : Complex)) * phi x)
    volume]
  apply integral_congr_ae
  filter_upwards with x
  rw [phi.even]
  congr 2
  push_cast
  ring

private theorem cayley_moment_inv
    (a : Real) (ha : 0 < a) (phi : WeilTestFunction) (z : Circle) :
    cayleyMomentFunction a phi z⁻¹ = cayleyMomentFunction a phi z := by
  by_cases hz : z = 1
  · subst z
    simp
  · let xi : Real := cayleyInverse a z
    have hzrepr : cayleyCircle a ha xi = z := cayley_circle_inverse a ha z hz
    rw [← hzrepr, ← cayley_circle_neg]
    rw [cayleyMomentFunction,
      if_neg (cayley_circle_ne_one a ha (-xi)), cayley_inverse_circle]
    rw [cayleyMomentFunction,
      if_neg (cayley_circle_ne_one a ha xi), cayley_inverse_circle]
    rw [show fourierLaplace phi ((-xi : Real) : Complex) =
        fourierLaplace phi (xi : Complex) by
      simpa only [Complex.ofReal_neg] using fourier_laplace_neg phi xi]
    congr 2
    ring

private theorem finite_positive_cubature
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (d : Nat) (mu : FiniteMeasure X) (s : Finset X)
    (hae : ∀ᵐ x ∂(mu : Measure X), x ∈ s)
    (moment : Fin d → X → Real) :
    ∃ (ι : Type) (_ : Fintype ι) (point : ι → X) (weight : ι → Real),
      Fintype.card ι ≤ d + 1 ∧
      (∀ r, 0 < weight r) ∧
      (∀ r, point r ∈ s) ∧
      (∑ r, weight r) = (mu : Measure X).real univ ∧
      ∀ i, ∫ x, moment i x ∂(∑ r, ENNReal.ofReal (weight r) • Measure.dirac (point r)) =
        ∫ x, moment i x ∂(mu : Measure X) := by
  classical
  by_cases hmu : mu = 0
  · subst mu
    refine ⟨Fin 0, inferInstance, Fin.elim0, Fin.elim0, by simp, ?_, ?_, by simp, ?_⟩
    · intro r
      exact Fin.elim0 r
    · intro r
      exact Fin.elim0 r
    · intro i
      simp
  let t : Finset X := s.filter fun x => (mu : Measure X) {x} ≠ 0
  have hdecomp :
      (mu : Measure X) = ∑ x ∈ t, (mu : Measure X) {x} • Measure.dirac x := by
    have hsdecomp := Measure.ae_mem_finset_iff.mp hae
    apply hsdecomp.trans
    simp only [t, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hpos : (mu : Measure X) {x} ≠ 0
    · simp [hpos]
    · have hzero : (mu : Measure X) {x} = 0 := not_ne_iff.mp hpos
      simp [hzero]
  have ht_ae : ∀ᵐ x ∂(mu : Measure X), x ∈ t :=
    Measure.ae_mem_finset_iff.mpr hdecomp
  let mass : Real := (mu : Measure X).real univ
  have hmass : 0 < mass := by
    have hmeasure : (mu : Measure X) ≠ 0 := by
      intro hzero
      apply hmu
      exact FiniteMeasure.toMeasure_injective hzero
    letI : NeZero (mu : Measure X) := ⟨hmeasure⟩
    exact measureReal_univ_pos
  let rawWeight : X → Real := fun x => (mu : Measure X).real {x} / mass
  have hsum_singletons : (∑ x ∈ t, (mu : Measure X).real {x}) = mass := by
    rw [MeasureTheory.sum_measureReal_singleton]
    change (mu : Measure X).real (t : Set X) = (mu : Measure X).real univ
    rw [measureReal_def, measureReal_def]
    congr 1
    exact MeasureTheory.measure_of_measure_compl_eq_zero (mem_ae_iff.mp ht_ae)
  have hweightsum : ∑ x ∈ t, rawWeight x = 1 := by
    simp only [rawWeight, ← Finset.sum_div]
    rw [hsum_singletons, div_self hmass.ne']
  have hweight_nonneg : ∀ x ∈ t, 0 ≤ rawWeight x := by
    intro x hx
    exact div_nonneg (measureReal_nonneg) hmass.le
  let vector : X → (Fin d → Real) := fun x i => moment i x
  let center : Fin d → Real := ∑ x ∈ t, rawWeight x • vector x
  have hcenter : center ∈ convexHull Real (vector '' (t : Set X)) := by
    have hmass_center := Finset.centerMass_mem_convexHull
      (s := vector '' (t : Set X)) t hweight_nonneg
      (by rw [hweightsum]; exact zero_lt_one)
      (fun x hx => show vector x ∈ vector '' (t : Set X) from ⟨x, hx, rfl⟩)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hweightsum] at hmass_center
    exact hmass_center
  obtain ⟨ι, inst, values, weights, hvalues, hindependent, hweights_pos,
      hweights_one, hcenter_eq⟩ := eq_pos_convex_span_of_mem_convexHull hcenter
  letI : Fintype ι := inst
  choose point hpoint_mem hpoint_value using fun r => hvalues (Set.mem_range_self r)
  let weight : ι → Real := fun r => mass * weights r
  refine ⟨ι, inst, point, weight, ?_, ?_,
    (fun r => (Finset.mem_filter.mp (hpoint_mem r)).1), ?_, ?_⟩
  · calc
      Fintype.card ι ≤ Module.finrank Real
          (vectorSpan Real (Set.range values)) + 1 := hindependent.card_le_finrank_succ
      _ ≤ Module.finrank Real (Fin d → Real) + 1 := by
        exact Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = d + 1 := by simp
  · intro r
    exact mul_pos hmass (hweights_pos r)
  · simp only [weight, ← Finset.mul_sum]
    rw [hweights_one, mul_one]
  · intro i
    have hleft :
        (∫ x, moment i x ∂(∑ r, ENNReal.ofReal (weight r) • Measure.dirac (point r))) =
          ∑ r, weight r * moment i (point r) := by
      rw [integral_finsetSum_measure]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [integral_smul_measure, integral_dirac]
        rw [ENNReal.toReal_ofReal (le_of_lt (mul_pos hmass (hweights_pos r)))]
        rfl
      · intro r hr
        apply Integrable.smul_measure (integrable_dirac (by simp))
        simp
    have hright :
        (∫ x, moment i x ∂(mu : Measure X)) =
          ∑ x ∈ t, (mu : Measure X).real {x} * moment i x := by
      calc
        (∫ x, moment i x ∂(mu : Measure X)) =
            ∫ x, moment i x ∂(∑ x ∈ t,
              (mu : Measure X) {x} • Measure.dirac x) :=
                congrArg (fun nu : Measure X => ∫ x, moment i x ∂nu) hdecomp
        _ = ∑ x ∈ t, (mu : Measure X).real {x} * moment i x := by
          rw [integral_finsetSum_measure]
          · apply Finset.sum_congr rfl
            intro x hx
            rw [integral_smul_measure, integral_dirac]
            rfl
          · intro x hx
            apply Integrable.smul_measure (integrable_dirac (by simp))
            finiteness
    rw [hleft, hright]
    have hcoordinate :
        (∑ r, weights r * values r i) = center i := by
      have := congrFun hcenter_eq i
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    calc
      (∑ r, weight r * moment i (point r)) =
          mass * ∑ r, weights r * values r i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            rw [← hpoint_value r]
            simp only [weight, vector]
            ring
      _ = mass * center i := by rw [hcoordinate]
      _ = ∑ x ∈ t, (mu : Measure X).real {x} * moment i x := by
        simp only [center, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vector]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [rawWeight]
        field_simp [hmass.ne']

private theorem active_contact_set_finite
    (a theta : Real) (ha : 0 < a) (htheta : 0 < theta) (phi : WeilTestFunction) :
    {z : Circle | cayleyMomentFunction a phi z + theta = 0}.Finite := by
  let realZeros : Set Real :=
    {xi : Real | (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
      fourierLaplace phi xi + theta) = 0}
  have hrealZeros : realZeros.Finite := active_real_zero_set_finite a theta htheta phi
  apply (hrealZeros.image (cayleyCircle a ha)).subset
  intro z hz
  have hzne : z ≠ 1 := by
    intro h
    subst z
    simp [cayleyMomentFunction, htheta.ne'] at hz
  let xi : Real := cayleyInverse a z
  have hxi : xi ∈ realZeros := by
    change (((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
      fourierLaplace phi xi + theta) = 0
    change cayleyMomentFunction a phi z + theta = 0 at hz
    rw [cayleyMomentFunction, if_neg hzne] at hz
    simpa only [xi, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_mul] using hz
  exact ⟨xi, hxi, cayley_circle_inverse a ha z hzne⟩

private theorem cayley_moment_im_eq_zero
    (a : Real) (phi : WeilTestFunction) (hreal : ∀ x, conj (phi x) = phi x)
    (z : Circle) :
    (cayleyMomentFunction a phi z).im = 0 := by
  classical
  by_cases hz : z = 1
  · simp [cayleyMomentFunction, hz]
  · rw [cayleyMomentFunction, if_neg hz]
    apply Complex.conj_eq_iff_im.mp
    rw [map_mul, Complex.conj_ofReal, fourierLaplace_real_axis phi hreal]

private theorem integral_complex_eq_of_real_part
    {X : Type*} [MeasurableSpace X]
    (f : X → Complex) (mu nu : Measure X)
    (hfmu : Integrable f mu) (hfnu : Integrable f nu)
    (him : ∀ x, (f x).im = 0)
    (hre : (∫ x, (f x).re ∂mu) = ∫ x, (f x).re ∂nu) :
    (∫ x, f x ∂mu) = ∫ x, f x ∂nu := by
  apply Complex.ext
  · calc
      (∫ x, f x ∂mu).re = ∫ x, (f x).re ∂mu := by
        simpa using (integral_re hfmu).symm
      _ = ∫ x, (f x).re ∂nu := hre
      _ = (∫ x, f x ∂nu).re := by
        simpa using integral_re hfnu
  · calc
      (∫ x, f x ∂mu).im = ∫ x, (f x).im ∂mu := by
        simpa using (integral_im hfmu).symm
      _ = 0 := by simp_rw [him]; simp
      _ = ∫ x, (f x).im ∂nu := by simp_rw [him]; simp
      _ = (∫ x, f x ∂nu).im := by
        simpa using integral_im hfnu

private theorem integrable_of_ae_mem_finset
    {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (f : X → E) (mu : Measure X) [IsFiniteMeasure mu] (s : Finset X)
    (hae : ∀ᵐ x ∂mu, x ∈ s) : Integrable f mu := by
  rw [Measure.ae_mem_finset_iff.mp hae]
  apply integrable_finsetSum_measure.2
  intro x hx
  apply Integrable.smul_measure
    (integrable_dirac (f := f) (a := x) (by exact enorm_lt_top))
  finiteness

/-- Positive active pressure turns a KKT-supported residual into a finite
contact completion, preserving its total residual mass and all finite real
observer moments. Each selected contact also determines a conjugate contact
orbit under circle inversion. -/
theorem active_finite_contact_completion
    (d : Nat) (a theta : Real) (alpha : NNReal) (ha : 0 < a)
    (htheta : 0 < theta) (phi : WeilTestFunction)
    (observer : Fin d → WeilTestFunction)
    (hobserverReal : ∀ i x, conj (observer i x) = observer i x)
    (sigma : FiniteMeasure Circle)
    (hsupport : (sigma : Measure Circle).support ⊆
      {z : Circle | cayleyMomentFunction a phi z + theta = 0}) :
    ∃ (ι : Type) (_ : Fintype ι) (point : ι → Circle) (weight : ι → Real)
        (muStar : Measure Circle),
      Fintype.card ι ≤ d + 1 ∧
      (∀ r, 0 < weight r) ∧
      (∀ r, cayleyMomentFunction a phi (point r) + theta = 0) ∧
      (∀ r, cayleyMomentFunction a phi (point r)⁻¹ + theta = 0) ∧
      (∑ r, weight r) = (sigma : Measure Circle).real univ ∧
      muStar = (alpha : ENNReal) •
          (normalizedCircleHaar : Measure Circle) +
        ∑ r, ENNReal.ofReal (weight r) • Measure.dirac (point r) ∧
      ∀ i,
        ∫ z, cayleyMomentFunction a (observer i) z
            ∂(∑ r, ENNReal.ofReal (weight r) • Measure.dirac (point r)) =
        ∫ z, cayleyMomentFunction a (observer i) z
          ∂(sigma : Measure Circle) := by
  classical
  let contact : Set Circle :=
    {z : Circle | cayleyMomentFunction a phi z + theta = 0}
  have hcontactFinite : contact.Finite := active_contact_set_finite a theta ha htheta phi
  let contactFinset : Finset Circle := hcontactFinite.toFinset
  have hsigmaContact : ∀ᵐ z ∂(sigma : Measure Circle), z ∈ contactFinset := by
    filter_upwards [Measure.support_mem_ae] with z hz
    exact hcontactFinite.mem_toFinset.mpr (hsupport hz)
  obtain ⟨ι, inst, point, weight, hcard, hweight, hpoint, hmass, hmomentsReal⟩ :=
    finite_positive_cubature d sigma contactFinset hsigmaContact
      (fun i z => (cayleyMomentFunction a (observer i) z).re)
  letI : Fintype ι := inst
  let atomic : Measure Circle :=
    ∑ r, ENNReal.ofReal (weight r) • Measure.dirac (point r)
  have hcomplexMoments : ∀ i,
      (∫ z, cayleyMomentFunction a (observer i) z ∂atomic) =
        ∫ z, cayleyMomentFunction a (observer i) z ∂(sigma : Measure Circle) := by
    intro i
    apply integral_complex_eq_of_real_part
    · dsimp only [atomic]
      apply integrable_finsetSum_measure.2
      intro r hr
      apply Integrable.smul_measure
        (integrable_dirac
          (f := fun z => cayleyMomentFunction a (observer i) z)
          (a := point r) (by exact enorm_lt_top))
      simp
    · exact integrable_of_ae_mem_finset _ (sigma : Measure Circle) _ hsigmaContact
    · exact cayley_moment_im_eq_zero a (observer i) (hobserverReal i)
    · exact hmomentsReal i
  let muStar : Measure Circle :=
    (alpha : ENNReal) • (normalizedCircleHaar : Measure Circle) + atomic
  refine ⟨ι, inst, point, weight, muStar, hcard, hweight, ?_, ?_, hmass, rfl, ?_⟩
  · intro r
    exact hcontactFinite.mem_toFinset.mp (hpoint r)
  · intro r
    rw [cayley_moment_inv a ha]
    exact hcontactFinite.mem_toFinset.mp (hpoint r)
  · exact hcomplexMoments

#print axioms active_finite_contact_completion

end D5.S3.Weil.TestFunctions.ActiveFiniteContactCompletion
