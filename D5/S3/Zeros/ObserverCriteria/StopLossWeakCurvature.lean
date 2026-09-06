/- GID: D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature
   generality: G
   mirror-B: D5/B/S3/Zeros/ObserverCriteria/StopLossWeakCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite stop-loss profiles have atomic weak curvature and tail transport. -/

import D5.S3.Zeros.ObservationDepthStopLoss
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/- Source provenance: observer-adelic-completion-constant-theory, observation-layer
   transport identities. The finite defect product is represented by the frozen
   ObservationDepthStopLoss primitives. Positive pole distances are unnecessary
   for these identities. Recovery of measures from distributions is not asserted.

   Library search: D5 has the primitives and bounds, but no weak curvature owner.
   Mathlib provides HasCompactSupport.integral_Iic_deriv_eq, indicator integration,
   finite-sum linearity and intervalIntegral.integral_Ioi_sub_Ioi. The new analytic
   construction is hpderiv + hsplit in active_pole_height_weak_curvature.
   remaining_depth_weak_curvature consumes that theorem for source weak curvature;
   stop_loss_transport_and_weak_curvature consumes remaining_depth_weak_curvature
   and the private transport helpers for the seven displayed source identities.
   Both finite-product declarations are bind-only companions of the single kink. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.ObserverCriteria.StopLossWeakCurvature

open MeasureTheory Set Filter Function
open scoped BigOperators Topology
open D5.S3.Zeros.ObservationDepthStopLoss

/-- The positive-part kink has a unit point mass as its weak second derivative. -/
theorem active_pole_height_weak_curvature (delta : ℝ) (phi : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 2 phi) (hsupport : HasCompactSupport phi) :
    (∫ x, activePoleHeight delta x * deriv (deriv phi) x) = phi delta := by
  have hphi' : ContDiff ℝ 1 (deriv phi) := hsmooth.deriv'
  let primitive : ℝ → ℝ := fun x => (delta - x) * deriv phi x + phi x
  have hpcont : ContDiff ℝ 1 primitive := by
    dsimp [primitive]
    exact ((contDiff_const.sub contDiff_id).mul hphi').add
      (hsmooth.of_le (by norm_num))
  have hpsupport : HasCompactSupport primitive :=
    hsupport.deriv.mul_left.add hsupport
  have hpderiv : deriv primitive = fun x => (delta - x) * deriv (deriv phi) x := by
    funext x
    have hd := (((hasDerivAt_const x delta).sub (hasDerivAt_id x)).mul
      (hphi'.differentiable (by norm_num) x).hasDerivAt).add
      (hsmooth.differentiable (by norm_num) x).hasDerivAt
    have hd' : HasDerivAt primitive
        ((0 - 1) * deriv phi x + (delta - x) * deriv (deriv phi) x + deriv phi x) x := hd
    rw [hd'.deriv]
    ring
  have hprimitive := hpsupport.integral_Iic_deriv_eq hpcont delta
  rw [hpderiv] at hprimitive
  have hsplit : (fun x => activePoleHeight delta x * deriv (deriv phi) x) =
      (Iic delta).indicator (fun x => (delta - x) * deriv (deriv phi) x) := by
    funext x
    by_cases hx : x ≤ delta
    · simp [activePoleHeight, hx, sub_nonneg.mpr hx]
    · simp [activePoleHeight, hx, (sub_neg.mpr (lt_of_not_ge hx)).le]
  rw [hsplit, integral_indicator measurableSet_Iic, hprimitive]
  simp [primitive]

private theorem kink_test_integrable (delta : ℝ) (phi : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 2 phi) (hsupport : HasCompactSupport phi) :
    Integrable (fun x => activePoleHeight delta x * deriv (deriv phi) x) := by
  have hphi' : ContDiff ℝ 1 (deriv phi) := hsmooth.deriv'
  have hphi'' : ContDiff ℝ 0 (deriv (deriv phi)) := hphi'.deriv'
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((continuous_const.sub continuous_id).max continuous_const).mul
      hphi''.continuous
  · exact hsupport.deriv.deriv.mul_left

/-- Companion for the finite defect product: finite weak curvature consumes the
single-kink weak curvature identity term by term. -/
theorem remaining_depth_weak_curvature {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (phi : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 2 phi) (hsupport : HasCompactSupport phi) :
    (∫ x, remainingDepth delta multiplicity x * deriv (deriv phi) x) =
      ∑ j, (multiplicity j : ℝ) * phi (delta j) := by
  simp_rw [remainingDepth, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun j _ =>
    (kink_test_integrable (delta j) phi hsmooth hsupport).const_mul _)]
  simp_rw [integral_const_mul,
    active_pole_height_weak_curvature _ phi hsmooth hsupport]

private theorem decay_eq_sub {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega y : ℝ) (hy : 0 ≤ y) :
    doubleDepthDecay delta multiplicity omega y =
      remainingDepth delta multiplicity omega -
        remainingDepth delta multiplicity (omega + y) := by
  unfold doubleDepthDecay remainingDepth
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold activePoleHeight
  have h : min y (max (delta j - omega) 0) =
      max (delta j - omega) 0 - max (delta j - (omega + y)) 0 := by
    rcases le_total (delta j) omega with h | h
    · rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_right hy]
      ring
    · rw [max_eq_left (by linarith)]
      rcases le_total y (delta j - omega) with h' | h'
      · rw [min_eq_left h', max_eq_left (by linarith)]
        ring
      · rw [min_eq_right h', max_eq_right (by linarith)]
        ring
  rw [h]
  ring

private theorem tail_integrable (delta omega c : ℝ) :
    IntegrableOn ((Iio delta).indicator (fun _ : ℝ => c)) (Ioi omega) := by
  rw [integrableOn_indicator_iff measurableSet_Iio]
  have hi : Iio delta ∩ Ioi omega = Ioo omega delta := by ext x; simp [and_comm]
  rw [hi]
  exact integrableOn_const (by simp [Real.volume_Ioo])

private theorem integral_tail (delta omega c : ℝ) :
    (∫ x in Ioi omega, (Iio delta).indicator (fun _ : ℝ => c) x) =
      c * activePoleHeight delta omega := by
  rw [setIntegral_indicator measurableSet_Iio]
  have hi : Ioi omega ∩ Iio delta = Ioo omega delta := by ext x; simp
  rw [hi, setIntegral_const, Real.volume_real_Ioo]
  simp [activePoleHeight, mul_comm]

private theorem tail_count_eq {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (x : ℝ) :
    (horizontalTailCount delta multiplicity x : ℝ) =
      ∑ j, (Iio (delta j)).indicator (fun _ : ℝ => (multiplicity j : ℝ)) x := by
  simp [horizontalTailCount, Set.indicator, Nat.cast_sum, Nat.cast_ite]

private theorem tail_count_integrable {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega : ℝ) :
    IntegrableOn (fun x => (horizontalTailCount delta multiplicity x : ℝ)) (Ioi omega) := by
  simp_rw [tail_count_eq]
  exact integrable_finsetSum _ fun j _ => tail_integrable (delta j) omega _

private theorem remaining_eq_integral {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega : ℝ) :
    remainingDepth delta multiplicity omega =
      ∫ x in Ioi omega, (horizontalTailCount delta multiplicity x : ℝ) := by
  simp_rw [tail_count_eq]
  rw [integral_finsetSum _ (fun j _ => tail_integrable (delta j) omega _)]
  simp_rw [integral_tail]
  rfl

private theorem hasDerivAt_height (delta omega : ℝ) (h : omega ≠ delta) :
    HasDerivAt (activePoleHeight delta) (if omega < delta then -1 else 0) omega := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [if_pos h]
    apply ((hasDerivAt_id omega).const_sub delta).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds h] with x hx
    simp [activePoleHeight, sub_nonneg.mpr hx.le]
  · rw [if_neg h.not_gt]
    apply (hasDerivAt_const omega (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h] with x hx
    simp [activePoleHeight, sub_nonpos.mpr hx.le]

private theorem hasDerivAt_remaining {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega : ℝ)
    (h : ∀ j, omega ≠ delta j) :
    HasDerivAt (remainingDepth delta multiplicity)
      (-(horizontalTailCount delta multiplicity omega : ℝ)) omega := by
  have hs : -(horizontalTailCount delta multiplicity omega : ℝ) =
      ∑ j, (multiplicity j : ℝ) * (if omega < delta j then -1 else 0) := by
    simp only [horizontalTailCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hs]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasDerivAt_height (delta j) omega (h j)).const_mul (multiplicity j : ℝ))

private theorem decay_derivatives {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) (omega y : ℝ) (hy : 0 < y)
    (hleft : ∀ j, omega ≠ delta j) (hright : ∀ j, omega + y ≠ delta j) :
    HasDerivAt (fun t => doubleDepthDecay delta multiplicity omega t)
        (horizontalTailCount delta multiplicity (omega + y) : ℝ) y ∧
      HasDerivAt (fun t => doubleDepthDecay delta multiplicity t y)
        ((horizontalTailCount delta multiplicity (omega + y) : ℝ) -
          (horizontalTailCount delta multiplicity omega : ℝ)) omega := by
  have hr := hasDerivAt_remaining delta multiplicity (omega + y) hright
  constructor
  · have hd := (hasDerivAt_const y (remainingDepth delta multiplicity omega)).sub
      (hr.comp y ((hasDerivAt_id y).const_add omega))
    simp only [mul_one, zero_sub, neg_neg] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hy] with t ht
    exact decay_eq_sub delta multiplicity omega t ht.le
  · have hd := (hasDerivAt_remaining delta multiplicity omega hleft).sub
      (hr.comp omega ((hasDerivAt_id omega).add_const y))
    simp only [mul_one, sub_neg_eq_add, neg_add_eq_sub] at hd
    apply hd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun t => decay_eq_sub delta multiplicity t y hy.le

/-- Named transport companion: all seven displayed source identities, with weak
curvature supplied by remaining_depth_weak_curvature. Measure recovery is separate. -/
theorem stop_loss_transport_and_weak_curvature {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (multiplicity : ι → ℕ) :
    (∀ omega : ℝ, remainingDepth delta multiplicity omega =
      ∫ x in Ioi omega, (horizontalTailCount delta multiplicity x : ℝ)) ∧
    (∀ omega y : ℝ, 0 ≤ y → doubleDepthDecay delta multiplicity omega y =
      remainingDepth delta multiplicity omega - remainingDepth delta multiplicity (omega + y)) ∧
    (∀ omega y : ℝ, 0 ≤ y → doubleDepthDecay delta multiplicity omega y =
      ∫ x in omega..omega + y, (horizontalTailCount delta multiplicity x : ℝ)) ∧
    (∀ omega y : ℝ, 0 < y → (∀ j, omega + y ≠ delta j) →
      deriv (fun t => doubleDepthDecay delta multiplicity omega t) y =
        (horizontalTailCount delta multiplicity (omega + y) : ℝ)) ∧
    (∀ omega y : ℝ, 0 ≤ y → (∀ j, omega ≠ delta j) →
      (∀ j, omega + y ≠ delta j) →
      deriv (fun t => doubleDepthDecay delta multiplicity t y) omega =
        (horizontalTailCount delta multiplicity (omega + y) : ℝ) -
          (horizontalTailCount delta multiplicity omega : ℝ)) ∧
    (∀ omega y : ℝ, 0 < y → (∀ j, omega ≠ delta j) →
      (∀ j, omega + y ≠ delta j) →
      deriv (fun t => doubleDepthDecay delta multiplicity t y) omega -
        deriv (fun t => doubleDepthDecay delta multiplicity omega t) y =
          -(horizontalTailCount delta multiplicity omega : ℝ)) ∧
    (∀ phi : ℝ → ℝ, ContDiff ℝ 2 phi → HasCompactSupport phi →
      (∫ x, remainingDepth delta multiplicity x * deriv (deriv phi) x) =
        ∑ j, (multiplicity j : ℝ) * phi (delta j)) := by
  refine ⟨remaining_eq_integral delta multiplicity, decay_eq_sub delta multiplicity,
    ?_, ?_, ?_, ?_, remaining_depth_weak_curvature delta multiplicity⟩
  · intro omega y hy
    rw [decay_eq_sub delta multiplicity omega y hy,
      remaining_eq_integral, remaining_eq_integral]
    exact intervalIntegral.integral_Ioi_sub_Ioi
      (tail_count_integrable delta multiplicity omega) (by linarith)
  · intro omega y hy hright
    have hr := hasDerivAt_remaining delta multiplicity (omega + y) hright
    have hd := (hasDerivAt_const y (remainingDepth delta multiplicity omega)).sub
      (hr.comp y ((hasDerivAt_id y).const_add omega))
    simp only [mul_one, zero_sub, neg_neg] at hd
    exact (hd.congr_of_eventuallyEq (by
      filter_upwards [eventually_gt_nhds hy] with t ht
      exact decay_eq_sub delta multiplicity omega t ht.le)).deriv
  · intro omega y hy hleft hright
    have hd := (hasDerivAt_remaining delta multiplicity omega hleft).sub
      ((hasDerivAt_remaining delta multiplicity (omega + y) hright).comp omega
        ((hasDerivAt_id omega).add_const y))
    simp only [mul_one, sub_neg_eq_add, neg_add_eq_sub] at hd
    exact (hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => decay_eq_sub delta multiplicity t y hy)).deriv
  · intro omega y hy hleft hright
    obtain ⟨hdY, hdOmega⟩ := decay_derivatives delta multiplicity omega y hy hleft hright
    rw [hdY.deriv, hdOmega.deriv]
    ring

-- Checked inhabitance and satisfiability, not additional deposited claims.
example : Nonempty (Unit → ℝ) := ⟨fun _ => 1⟩
example : ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ)) ∧
    HasCompactSupport (fun _ : ℝ => (0 : ℝ)) :=
  ⟨contDiff_const, by simp [HasCompactSupport]⟩

#print axioms active_pole_height_weak_curvature
#print axioms remaining_depth_weak_curvature
#print axioms stop_loss_transport_and_weak_curvature

end D5.S3.Zeros.ObserverCriteria.StopLossWeakCurvature
