/- GID: D5/S3/Analytic/WallisRemainder/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/WallisRemainder/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Strict monotonicity and reciprocal nonvanishing for three Wallis gamma remainders. -/

import D5.S3.Analytic.WallisRemainder.Defs
import D5.S3.Analytic.WallisRemainder.Stieltjes
import D5.S3.Analytic.WallisRemainder.Measure
import D5.S3.Analytic.WallisRemainder.Laplace
import Mathlib.Tactic
open D5.S3.Analytic.WallisRemainder.Defs
open D5.S3.Analytic.WallisRemainder.Stieltjes
open D5.S3.Analytic.WallisRemainder.Measure
open MeasureTheory Filter Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Analytic.WallisRemainder.Result
private lemma theta_algebra {x s : ℝ} (hx : 0 < x)
    (hr : -Real.log (wallisB x) = x/8*s) :
    theta x = -(x^2)^3 * (s-1/(x^2+1/24))/(31/2880) := by
  have hd : x^2+1/24 ≠ 0 := ne_of_gt (by positivity)
  have he : 24*x^2+1 ≠ 0 := ne_of_gt (by positivity)
  have hl : Real.log (wallisB x) = -(x/8*s) := by linarith
  rw [theta, hl]
  field_simp
  <;> ring

private lemma chi_algebra {x s q : ℝ} (hx : 0 < x)
    (hr : -Real.log (wallisB x) = x/8*s)
    (hq : x^2*s = 1-q/24) :
    chi x = (x^2)^3 * (q-1/(x^2+3/10))/(771/5600) := by
  have hd : x^2+3/10 ≠ 0 := ne_of_gt (by positivity)
  have he : 10*x^2+3 ≠ 0 := ne_of_gt (by positivity)
  have hl : Real.log (wallisB x) = -(x/8*s) := by linarith
  have hs : s = (1-q/24)/x^2 := by
    apply (eq_div_iff (sq_pos_of_pos hx).ne').mpr
    nlinarith [hq]
  rw [chi, hl, hs]
  field_simp
  <;> ring

private lemma mu_algebra {x s q : ℝ} (hx : 0 < x) (hs : 0 < s) (hqpos : 0 < q)
    (hr : -Real.log (wallisB x) = x/8*s)
    (hq : x^2*s = 1-q/24) :
    Real.log (wallisB x) ≠ 0 ∧
      (3/x)*(Real.log (wallisB x))⁻¹+24 ≠ 0 ∧
      mu x = 1/q-x^2-1/24 := by
  have hl : Real.log (wallisB x) = -(x/8*s) := by linarith
  have hn : Real.log (wallisB x) ≠ 0 := by
    rw [hl]
    exact neg_ne_zero.mpr (mul_ne_zero (div_ne_zero hx.ne' (by norm_num)) hs.ne')
  have hbr : (3/x)*(Real.log (wallisB x))⁻¹+24 = -q/(x^2*s) := by
    rw [hl]
    field_simp
    nlinarith [hq]
  refine ⟨hn, ?_, ?_⟩
  · rw [hbr]; exact div_ne_zero (neg_ne_zero.mpr hqpos.ne') (mul_pos (sq_pos_of_pos hx) hs).ne'
  · rw [mu, hbr]
    field_simp
    nlinarith [hq]
private lemma size_bias_identity {z : ℝ} (hz : 0 < z) :
    z * stieltjes P z = 1 - stieltjes Q z / 24 := by
  have hs : Integrable (fun v : ℝ => 1/(z+v)) P := integrable_resolvent P_pos hz
  have he : (fun v : ℝ => v*(1/(z+v))) =ᵐ[P]
      (fun v => 1-z*(1/(z+v))) := by
    filter_upwards [P_pos] with v hv
    have hn : z+v ≠ 0 := ne_of_gt (by linarith)
    field_simp
    <;> ring
  change z * (∫ v : ℝ, 1/(z+v) ∂P) = 1-(∫ v : ℝ, 1/(z+v) ∂Q)/24
  rw [integral_Q, integral_congr_ae he,
    integral_sub (f := fun _ : ℝ => 1) (g := fun v => z*(1/(z+v)))
      (integrable_const 1) (hs.const_mul z), integral_const_mul]
  simp [stieltjes]
  <;> ring

private lemma centered_P : (∫ v : ℝ, (v-(1/24 : ℝ))^2 ∂P) = 31/2880 := by
  rw [← integral_P_id, ← ProbabilityTheory.variance_eq_integral (by fun_prop), variance_P]

private lemma centered_Q : (∫ v : ℝ, (v-(3/10 : ℝ))^2 ∂Q) = 771/5600 := by
  rw [← integral_Q_id, ← ProbabilityTheory.variance_eq_integral (by fun_prop), variance_Q]

private lemma centered_integrable {M : MeasureTheory.Measure ℝ} [IsProbabilityMeasure M]
    (hi : Integrable (fun v : ℝ => v^2) M) (a : ℝ) :
    Integrable (fun v : ℝ => (v-a)^2) M := by
  have hm : MemLp (fun v : ℝ => v) 2 M :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hi
  exact (hm.sub (memLp_const a)).integrable_sq

private lemma Q_not_const (a : ℝ) : ¬ ∀ᵐ v ∂Q, v=a := by
  intro h
  have hh := ProbabilityTheory.variance_congr h
  rw [variance_Q] at hh
  have hc : ProbabilityTheory.variance (fun _ : ℝ => a) Q = 0 := by
    rw [ProbabilityTheory.variance_eq_integral measurable_const.aemeasurable]
    simp
  rw [hc] at hh
  norm_num at hh

private lemma result_of_representation
    (hr : ∀ x : ℝ, 0 < x → -Real.log (wallisB x) = x/8*stieltjes P (x^2)) :
    claim := by
  have hp : StrictMonoOn (jensenRemainder P (1/24) (31/2880)) (Ioi 0) := by
    have hh := strictMonoOn_jensenRemainder P_pos integrable_P_id
      (centered_integrable integrable_P_sq (1/24)) integral_P_id
      (show 0 < ∫ v : ℝ, (v-(1/24 : ℝ))^2 ∂P by rw [centered_P]; norm_num)
    simpa only [centered_P] using hh
  have hq : StrictMonoOn (jensenRemainder Q (3/10) (771/5600)) (Ioi 0) := by
    have hh := strictMonoOn_jensenRemainder Q_pos integrable_Q_id
      (centered_integrable integrable_Q_sq (3/10)) integral_Q_id
      (show 0 < ∫ v : ℝ, (v-(3/10 : ℝ))^2 ∂Q by rw [centered_Q]; norm_num)
    simpa only [centered_Q] using hh
  have hH := strictMonoOn_inv_stieltjes_sub Q_pos Q_not_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := mu_algebra hx (stieltjes_bounds P_pos (sq_pos_of_pos hx)).1
      (stieltjes_bounds Q_pos (sq_pos_of_pos hx)).1 (hr x hx)
      (size_bias_identity (sq_pos_of_pos hx))
    exact ⟨h.1,h.2.1⟩
  · intro x hx y hy hxy
    change 0<x at hx
    change 0<y at hy
    have hmx := (mu_algebra hx (stieltjes_bounds P_pos (sq_pos_of_pos hx)).1
      (stieltjes_bounds Q_pos (sq_pos_of_pos hx)).1 (hr x hx)
      (size_bias_identity (sq_pos_of_pos hx))).2.2
    have hmy := (mu_algebra hy (stieltjes_bounds P_pos (sq_pos_of_pos hy)).1
      (stieltjes_bounds Q_pos (sq_pos_of_pos hy)).1 (hr y hy)
      (size_bias_identity (sq_pos_of_pos hy))).2.2
    rw [hmx,hmy]
    exact sub_lt_sub_right (hH (sq_pos_of_pos hx) (sq_pos_of_pos hy)
      (by nlinarith)) _
  · intro x hx y hy hxy
    change 0<x at hx
    change 0<y at hy
    rw [theta_algebra hx (hr x hx), theta_algebra hy (hr y hy)]
    simpa only [jensenRemainder, neg_div, neg_mul] using
      neg_lt_neg (hp (sq_pos_of_pos hx) (sq_pos_of_pos hy) (by nlinarith))
  · intro x hx y hy hxy
    change 0<x at hx
    change 0<y at hy
    rw [chi_algebra hx (hr x hx) (size_bias_identity (sq_pos_of_pos hx)),
      chi_algebra hy (hr y hy) (size_bias_identity (sq_pos_of_pos hy))]
    exact hq (sq_pos_of_pos hx) (sq_pos_of_pos hy) (by nlinarith)

/-- Strict monotonicity and reciprocal nonvanishing for the Wallis remainders. -/
theorem result : claim := result_of_representation (fun _ hx => r_eq_stieltjes hx)

end D5.S3.Analytic.WallisRemainder.Result
