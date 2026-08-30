/- GID: D5/S3/Analytic/Adelic/OffLineCurvatureDipole
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/OffLineCurvatureDipole
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A reflected off-line pair induces a zero-mass curvature dipole. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/- Library-search audit trail (2026-08-30):
   * Exact-name and rational-function body-shape searches found no frozen D5
     owner for the off-line curvature formula together with its center, zero
     set, total mass, and sign profile.
   * `RelativeCurvatureSupportCriterion` concerns the support of a complex
     zero measure, while `BodeWidthCriterion` concerns a finite hyperbolic
     damping defect. Neither is a statement on this real curvature carrier.
   * Body-shape searches for the two reflected squared-distance logarithms
     found no canonical D5 potential primitive. The source potential is
     therefore constructed directly in the public statement, without a new
     definition.
   * Pinned Mathlib supplies `Real.hasDerivAt_log`,
     `integrable_inv_one_add_sq`, and
     `integral_of_hasDerivAt_of_tendsto`. These are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.OffLineCurvatureDipole

open Filter MeasureTheory
open scoped Topology

private theorem curvature_formula (delta gamma t : ℝ) (hdelta : 0 < delta) :
    let potential := fun u : ℝ =>
      Real.log ((u - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
        Real.log ((u + delta) ^ 2 + (t - gamma) ^ 2) / 2
    deriv (deriv potential) 0 =
      2 * (((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2) := by
  dsimp only
  let firstDerivative := fun u : ℝ =>
    (u - delta) / ((u - delta) ^ 2 + (t - gamma) ^ 2) +
      (u + delta) / ((u + delta) ^ 2 + (t - gamma) ^ 2)
  have hfirst (u : ℝ) (hu : |u| < delta) :
      HasDerivAt
        (fun v : ℝ =>
          Real.log ((v - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
            Real.log ((v + delta) ^ 2 + (t - gamma) ^ 2) / 2)
        (firstDerivative u) u := by
    have huBounds := abs_lt.mp hu
    have hminus : u - delta ≠ 0 := by linarith
    have hplus : u + delta ≠ 0 := by linarith
    have hminusDen : (u - delta) ^ 2 + (t - gamma) ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_ne_zero hminus, sq_nonneg (t - gamma)]
    have hplusDen : (u + delta) ^ 2 + (t - gamma) ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_ne_zero hplus, sq_nonneg (t - gamma)]
    have hminusInner :
        HasDerivAt
          (fun v : ℝ => (v - delta) ^ 2 + (t - gamma) ^ 2)
          (2 * (u - delta)) u := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one] using
        (((hasDerivAt_id u).sub_const delta).pow 2).add_const
          ((t - gamma) ^ 2)
    have hplusInner :
        HasDerivAt
          (fun v : ℝ => (v + delta) ^ 2 + (t - gamma) ^ 2)
          (2 * (u + delta)) u := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one] using
        (((hasDerivAt_id u).add_const delta).pow 2).add_const
          ((t - gamma) ^ 2)
    have hminusLog :
        HasDerivAt
          (fun v : ℝ =>
            Real.log ((v - delta) ^ 2 + (t - gamma) ^ 2) / 2)
          ((u - delta) / ((u - delta) ^ 2 + (t - gamma) ^ 2)) u := by
      have hraw := (hminusInner.log hminusDen).div_const 2
      refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      ring
    have hplusLog :
        HasDerivAt
          (fun v : ℝ =>
            Real.log ((v + delta) ^ 2 + (t - gamma) ^ 2) / 2)
          ((u + delta) / ((u + delta) ^ 2 + (t - gamma) ^ 2)) u := by
      have hraw := (hplusInner.log hplusDen).div_const 2
      refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      ring
    exact hminusLog.add hplusLog
  have hderivEventually :
      (fun u : ℝ => deriv
        (fun v : ℝ =>
          Real.log ((v - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
            Real.log ((v + delta) ^ 2 + (t - gamma) ^ 2) / 2) u)
        =ᶠ[𝓝 0] firstDerivative := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hdelta] with u hu
    apply (hfirst u ?_).deriv
    simpa [Metric.mem_ball, Real.dist_eq] using hu
  have hminusDenZero : delta ^ 2 + (t - gamma) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hdelta, sq_nonneg (t - gamma)]
  have hplusDenZero : delta ^ 2 + (t - gamma) ^ 2 ≠ 0 := hminusDenZero
  have hminusAtZero :
      HasDerivAt
        (fun u : ℝ => (u - delta) /
          ((u - delta) ^ 2 + (t - gamma) ^ 2))
        (((t - gamma) ^ 2 - delta ^ 2) /
          (delta ^ 2 + (t - gamma) ^ 2) ^ 2) 0 := by
    have hnum : HasDerivAt (fun u : ℝ => u - delta) 1 0 := by
      simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).sub_const delta
    have hden :
        HasDerivAt (fun u : ℝ => (u - delta) ^ 2 + (t - gamma) ^ 2)
          (-2 * delta) 0 := by
      have hraw := (hnum.pow 2).add_const ((t - gamma) ^ 2)
      refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      ring
    have hdenAtZero : (0 - delta) ^ 2 + (t - gamma) ^ 2 ≠ 0 := by
      simpa only [zero_sub, neg_sq] using hminusDenZero
    have hraw := hnum.div hden hdenAtZero
    refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    field_simp [hminusDenZero]
    ring
  have hplusAtZero :
      HasDerivAt
        (fun u : ℝ => (u + delta) /
          ((u + delta) ^ 2 + (t - gamma) ^ 2))
        (((t - gamma) ^ 2 - delta ^ 2) /
          (delta ^ 2 + (t - gamma) ^ 2) ^ 2) 0 := by
    have hnum : HasDerivAt (fun u : ℝ => u + delta) 1 0 := by
      simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).add_const delta
    have hden :
        HasDerivAt (fun u : ℝ => (u + delta) ^ 2 + (t - gamma) ^ 2)
          (2 * delta) 0 := by
      have hraw := (hnum.pow 2).add_const ((t - gamma) ^ 2)
      refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      ring
    have hdenAtZero : (0 + delta) ^ 2 + (t - gamma) ^ 2 ≠ 0 := by
      simpa only [zero_add] using hplusDenZero
    have hraw := hnum.div hden hdenAtZero
    refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    field_simp [hplusDenZero]
    ring
  have hsecond :
      HasDerivAt firstDerivative
        (2 * (((t - gamma) ^ 2 - delta ^ 2) /
          ((t - gamma) ^ 2 + delta ^ 2) ^ 2)) 0 := by
    dsimp only [firstDerivative]
    have hraw := hminusAtZero.add hplusAtZero
    refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    field_simp [hminusDenZero]
    ring
  exact (hsecond.congr_of_eventuallyEq hderivEventually).deriv

private theorem rational_curvature_integrable
    (delta gamma : ℝ) (hdelta : 0 < delta) :
    Integrable (fun t : ℝ =>
      2 * (((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2)) := by
  have hscaled : Integrable (fun t : ℝ => (1 + (t / delta) ^ 2)⁻¹) := by
    simpa [div_eq_inv_mul] using
      integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hdelta.ne')
  have hshifted :
      Integrable (fun t : ℝ => (1 + ((t - gamma) / delta) ^ 2)⁻¹) := by
    simpa [sub_eq_add_neg] using hscaled.comp_add_right (-gamma)
  have hmajor :
      Integrable (fun t : ℝ => 2 / ((t - gamma) ^ 2 + delta ^ 2)) := by
    convert hshifted.const_mul (2 / delta ^ 2) using 1
    funext t
    field_simp [hdelta.ne']
    ring
  refine hmajor.mono' ?_ (ae_of_all _ fun t => ?_)
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul continuous_const
    apply Continuous.div
    · exact ((continuous_id.sub continuous_const).pow 2).sub continuous_const
    · exact (((continuous_id.sub continuous_const).pow 2).add continuous_const).pow 2
    · intro t
      exact pow_ne_zero 2 (by
        nlinarith [sq_nonneg (t - gamma), sq_pos_of_pos hdelta])
  · have hden : 0 < (t - gamma) ^ 2 + delta ^ 2 := by
      nlinarith [sq_nonneg (t - gamma), sq_pos_of_pos hdelta]
    have hnum : |(t - gamma) ^ 2 - delta ^ 2| ≤
        (t - gamma) ^ 2 + delta ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (t - gamma), sq_nonneg delta]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_div, abs_pow, abs_of_pos hden]
    calc
      2 * (|(t - gamma) ^ 2 - delta ^ 2| /
          ((t - gamma) ^ 2 + delta ^ 2) ^ 2) ≤
          2 * (((t - gamma) ^ 2 + delta ^ 2) /
            ((t - gamma) ^ 2 + delta ^ 2) ^ 2) := by
        gcongr
      _ = 2 / ((t - gamma) ^ 2 + delta ^ 2) := by
        field_simp [hden.ne']

private theorem rational_curvature_integral
    (delta gamma : ℝ) (hdelta : 0 < delta) :
    ∫ t : ℝ, 2 * (((t - gamma) ^ 2 - delta ^ 2) /
      ((t - gamma) ^ 2 + delta ^ 2) ^ 2) = 0 := by
  let primitive := fun t : ℝ =>
    -2 * (t - gamma) / ((t - gamma) ^ 2 + delta ^ 2)
  let curvature := fun t : ℝ =>
    2 * (((t - gamma) ^ 2 - delta ^ 2) /
      ((t - gamma) ^ 2 + delta ^ 2) ^ 2)
  have hderiv (t : ℝ) : HasDerivAt primitive (curvature t) t := by
    have hdenNe : (t - gamma) ^ 2 + delta ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (t - gamma), sq_pos_of_pos hdelta]
    have hnum : HasDerivAt (fun x : ℝ => -2 * (x - gamma)) (-2) t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).sub_const gamma).const_mul (-2)
    have hden :
        HasDerivAt (fun x : ℝ => (x - gamma) ^ 2 + delta ^ 2)
          (2 * (t - gamma)) t := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one] using
        (((hasDerivAt_id t).sub_const gamma).pow 2).add_const (delta ^ 2)
    dsimp only [primitive, curvature]
    have hraw := hnum.div hden hdenNe
    refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    field_simp [hdenNe]
    ring
  have htop : Tendsto primitive atTop (𝓝 0) := by
    have hx : Tendsto (fun t : ℝ => t - gamma) atTop atTop := by
      simpa only [id_eq, sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-gamma) tendsto_id
    have habs : Tendsto (fun t : ℝ => |t - gamma|) atTop atTop := by
      exact (tendsto_norm_atTop_atTop.comp hx).congr'
        (Eventually.of_forall fun _ => by simp only [Function.comp_apply, Real.norm_eq_abs])
    have hbound : Tendsto (fun t : ℝ => 2 / |t - gamma|) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop habs
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
    filter_upwards [habs.eventually_gt_atTop 0] with t ht
    have hden : 0 < (t - gamma) ^ 2 + delta ^ 2 := by
      nlinarith [sq_nonneg (t - gamma), sq_pos_of_pos hdelta]
    dsimp only [primitive]
    rw [Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_neg (by norm_num : (-2 : ℝ) < 0), abs_of_pos hden]
    apply (div_le_div_iff₀ hden ht).2
    nlinarith [sq_abs (t - gamma), sq_nonneg delta]
  have hbot : Tendsto primitive atBot (𝓝 0) := by
    have hx : Tendsto (fun t : ℝ => t - gamma) atBot atBot := by
      simpa only [id_eq, sub_eq_add_neg] using
        tendsto_atBot_add_const_right atBot (-gamma) tendsto_id
    have hneg : Tendsto (fun t : ℝ => -(t - gamma)) atBot atTop := by
      exact (tendsto_neg_atBot_atTop.comp hx).congr'
        (Eventually.of_forall fun _ => rfl)
    have habs : Tendsto (fun t : ℝ => |t - gamma|) atBot atTop := by
      exact (tendsto_norm_atTop_atTop.comp hneg).congr'
        (Eventually.of_forall fun _ => by
          simp only [Function.comp_apply, Real.norm_eq_abs, abs_neg])
    have hbound : Tendsto (fun t : ℝ => 2 / |t - gamma|) atBot (𝓝 0) :=
      tendsto_const_nhds.div_atTop habs
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
    filter_upwards [habs.eventually_gt_atTop 0] with t ht
    have hden : 0 < (t - gamma) ^ 2 + delta ^ 2 := by
      nlinarith [sq_nonneg (t - gamma), sq_pos_of_pos hdelta]
    dsimp only [primitive]
    rw [Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_neg (by norm_num : (-2 : ℝ) < 0), abs_of_pos hden]
    apply (div_le_div_iff₀ hden ht).2
    nlinarith [sq_abs (t - gamma), sq_nonneg delta]
  change ∫ t : ℝ, curvature t = 0
  simpa using integral_of_hasDerivAt_of_tendsto hderiv
    (rational_curvature_integrable delta gamma hdelta) hbot htop

/--
The second normal derivative at the critical axis of the logarithmic potential
of a reflected off-line pair is a real curvature dipole. Its public statement
records the formula, center value, exact zero set, meaningful zero total mass,
and the negative-core/positive-wing sign profile on the same constructed
curvature function.
-/
theorem off_line_curvature_dipole (delta gamma : ℝ) (hdelta : 0 < delta) :
    let potential := fun u t : ℝ =>
      Real.log ((u - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
        Real.log ((u + delta) ^ 2 + (t - gamma) ^ 2) / 2
    let curvature := fun t : ℝ => deriv (deriv (fun u => potential u t)) 0
    (∀ t, curvature t =
      2 * (((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2)) ∧
      curvature gamma = -(2 / delta ^ 2) ∧
      (∀ t, curvature t = 0 ↔ t = gamma - delta ∨ t = gamma + delta) ∧
      Integrable curvature ∧
      (∫ t : ℝ, curvature t) = 0 ∧
      (∀ t, |t - gamma| < delta → curvature t < 0) ∧
      (∀ t, delta < |t - gamma| → 0 < curvature t) := by
  dsimp only
  have hformula (t : ℝ) := curvature_formula delta gamma t hdelta
  refine ⟨hformula, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hformula]
    field_simp [hdelta.ne']
    ring
  · intro t
    rw [hformula]
    have hden : 0 < ((t - gamma) ^ 2 + delta ^ 2) ^ 2 := by
      positivity
    constructor
    · intro hzero
      have hnum : (t - gamma) ^ 2 = delta ^ 2 := by
        apply sub_eq_zero.mp
        have hquot :
            ((t - gamma) ^ 2 - delta ^ 2) /
              ((t - gamma) ^ 2 + delta ^ 2) ^ 2 = 0 := by
          exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
        exact (div_eq_zero_iff.mp hquot).resolve_right hden.ne'
      rcases eq_or_eq_neg_of_sq_eq_sq (t - gamma) delta hnum with h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (rfl | rfl) <;> field_simp [hdelta.ne'] <;> ring
  · exact (rational_curvature_integrable delta gamma hdelta).congr
      (ae_of_all _ fun t => hformula t |>.symm)
  · rw [integral_congr_ae (ae_of_all _ fun t => hformula t)]
    exact rational_curvature_integral delta gamma hdelta
  · intro t ht
    rw [hformula]
    have hsquare : (t - gamma) ^ 2 < delta ^ 2 := by
      rw [← sq_abs (t - gamma)]
      exact (sq_lt_sq₀ (abs_nonneg (t - gamma)) hdelta.le).2 ht
    have hden : 0 < ((t - gamma) ^ 2 + delta ^ 2) ^ 2 := by positivity
    exact mul_neg_of_pos_of_neg (by norm_num)
      (div_neg_of_neg_of_pos (sub_neg.mpr hsquare) hden)
  · intro t ht
    rw [hformula]
    have hsquare : delta ^ 2 < (t - gamma) ^ 2 := by
      rw [← sq_abs (t - gamma)]
      exact (sq_lt_sq₀ hdelta.le (abs_nonneg (t - gamma))).2 ht
    have hden : 0 < ((t - gamma) ^ 2 + delta ^ 2) ^ 2 := by positivity
    exact mul_pos (by norm_num) (div_pos (sub_pos.mpr hsquare) hden)

#print axioms off_line_curvature_dipole

end D5.S3.Analytic.Adelic.OffLineCurvatureDipole
