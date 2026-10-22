/- GID: D5/S3/Analytic/WallisRemainder/Stieltjes
   generality: G
   mirror-B: D5/B/S3/Analytic/WallisRemainder/Stieltjes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.Basic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Strict monotonicity of normalized Stieltjes remainders for positive probability laws. -/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
noncomputable section
namespace D5.S3.Analytic.WallisRemainder.Stieltjes
noncomputable def stieltjes (M : Measure ℝ) (z : ℝ) : ℝ := ∫ v, 1 / (z + v) ∂M
noncomputable def jensenRemainder (M : Measure ℝ) (a s z : ℝ) : ℝ :=
  z ^ 3 * (stieltjes M z - 1 / (z + a)) / s

private lemma integral_pos_of_not_zero {M : Measure ℝ} {f : ℝ → ℝ}
    (hi : Integrable f M) (hn : ∀ᵐ v ∂M, 0 ≤ f v) (hne : ¬ f =ᵐ[M] 0) :
    0 < ∫ v, f v ∂M := by
  exact lt_of_le_of_ne (integral_nonneg_of_ae hn)
    (fun h => hne ((integral_eq_zero_iff_of_nonneg_ae hn hi).mp h.symm))

private lemma integrable_resolvent {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v) {z : ℝ} (hz : 0 < z) :
    Integrable (fun v => 1 / (z + v)) M := by
  have hm : Measurable (fun v : ℝ => z+v) := measurable_const.add measurable_id
  have hm' : Measurable (fun v : ℝ => 1/(z+v)) := measurable_const.div hm
  apply (integrable_const (1 / z)).mono' hm'.aestronglyMeasurable
  filter_upwards [hp] with v hv
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by linarith))]
  exact one_div_le_one_div_of_le hz (by linarith)

private lemma stieltjes_pos {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v) {z : ℝ} (hz : 0 < z) : 0 < stieltjes M z := by
  apply integral_pos_of_not_zero (integrable_resolvent hp hz)
  · filter_upwards [hp] with v hv using (one_div_pos.mpr (by linarith)).le
  · intro he
    have hf : ∀ᵐ v ∂M, False := by
      filter_upwards [hp, he] with v hv he
      have : 0 < 1 / (z + v) := one_div_pos.mpr (by linarith)
      simpa using this.ne' he
    have he : M = 0 := by simpa using hf
    have ht : M Set.univ = 1 := measure_univ
    simp [he] at ht

private lemma centered_integrable {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v) {z a : ℝ} (hz : 0 < z)
    (hi : Integrable (fun v => (v-a)^2) M) :
    Integrable (fun v => (v-a)^2 / (z+v)) M := by
  simp_rw [div_eq_mul_inv]
  apply hi.mul_bdd (g := fun v : ℝ => (z+v)⁻¹)
    ((measurable_const.add measurable_id).inv.aestronglyMeasurable) (c := 1 / z)
  filter_upwards [hp] with v hv
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith : 0 < z+v))]
  simpa only [one_div] using (one_div_le_one_div_of_le hz (by linarith : z ≤ z+v))

private lemma remainder_identity {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v) {z a : ℝ} (hz : 0 < z) (ha : 0 < a)
    (hfirst : Integrable (fun v : ℝ => v) M)
    (hmean : ∫ v, v ∂M = a) :
    stieltjes M z - 1 / (z+a) =
      (∫ v, (v-a)^2 / (z+v) ∂M) / (z+a)^2 := by
  have hza : z+a ≠ 0 := ne_of_gt (by linarith)
  have hid : (fun v => (v-a)^2 / (z+v)) =ᵐ[M]
      (fun v => (z+a)^2 * (1/(z+v) - 1/(z+a)) + (v-a)) := by
    filter_upwards [hp] with v hv
    have hzv : z+v ≠ 0 := ne_of_gt (by linarith)
    field_simp
    <;> ring
  have hi1 : Integrable (fun v => (z+a)^2 * (1/(z+v)-1/(z+a))) M :=
    ((integrable_resolvent hp hz).sub (integrable_const (1/(z+a)))).const_mul _
  have hi2 : Integrable (fun v : ℝ => v-a) M := hfirst.sub (integrable_const a)
  rw [integral_congr_ae hid, integral_add hi1 hi2, integral_const_mul,
    integral_sub (f := fun v : ℝ => 1/(z+v)) (g := fun _ => 1/(z+a))
      (integrable_resolvent hp hz) (integrable_const (1/(z+a))),
    integral_sub (f := fun v : ℝ => v) (g := fun _ => a) hfirst (integrable_const a)]
  simp only [integral_const, probReal_univ, one_smul, hmean, sub_self, add_zero]
  dsimp [stieltjes]
  field_simp

private lemma ratio_strict {x y a : ℝ} (hx : 0 < x) (hxy : x < y) (ha : 0 < a) :
    x / (x+a) < y / (y+a) := by
  apply (div_lt_div_iff₀ (by linarith : 0 < x+a) (by linarith : 0 < y+a)).mpr
  nlinarith

private lemma kernel_strict {x y a v : ℝ} (hx : 0 < x) (hxy : x < y)
    (ha : 0 < a) (hv : 0 < v) :
    x^3 / ((x+a)^2 * (x+v)) < y^3 / ((y+a)^2 * (y+v)) := by
  have hr := ratio_strict hx hxy ha
  have hs := ratio_strict hx hxy hv
  have hxa : 0 < x/(x+a) := div_pos hx (by linarith)
  have hya : 0 < y/(y+a) := div_pos (by linarith) (by linarith)
  have hxv : 0 < x/(x+v) := div_pos hx (by linarith)
  have hyv : 0 < y/(y+v) := div_pos (by linarith) (by linarith)
  have hsq : (x/(x+a))^2 < (y/(y+a))^2 := by nlinarith
  have hmul := mul_lt_mul hsq hs.le hxv (sq_nonneg (y/(y+a)))
  convert hmul using 1 <;> field_simp

/-- Strict increase of the normalized Jensen remainder of a Stieltjes transform. -/
theorem strictMonoOn_jensenRemainder {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v) {a : ℝ}
    (hfirst : Integrable (fun v : ℝ => v) M)
    (hsecond : Integrable (fun v => (v-a)^2) M)
    (hmean : ∫ v, v ∂M = a) (hvar : 0 < ∫ v, (v-a)^2 ∂M) :
    StrictMonoOn (jensenRemainder M a (∫ v, (v-a)^2 ∂M)) (Ioi 0) := by
  have ha : 0 < a := by
    rw [← hmean]
    apply integral_pos_of_not_zero hfirst (hp.mono (fun v hv => hv.le))
    intro he
    have hf : ∀ᵐ v ∂M, False := by
      filter_upwards [hp, he] with v hv he using hv.ne' he
    have he : M = 0 := by simpa using hf
    have ht : M Set.univ = 1 := measure_univ
    simp [he] at ht
  intro x hx y hy hxy
  let f (z v : ℝ) := (v-a)^2 / (z+v) * (z^3 / (z+a)^2)
  have hi (z : ℝ) (hz : 0 < z) : Integrable (f z) M :=
    (centered_integrable hp hz hsecond).mul_const _
  have hf (z : ℝ) (hz : 0 < z) :
      jensenRemainder M a (∫ v, (v-a)^2 ∂M) z =
        (∫ v, f z v ∂M) / (∫ v, (v-a)^2 ∂M) := by
    rw [jensenRemainder, remainder_identity hp hz ha hfirst hmean,
      integral_mul_const]
    ring
  rw [hf x hx, hf y hy]
  apply (div_lt_div_iff_of_pos_right hvar).mpr
  have hle : f x ≤ᵐ[M] f y := by
    filter_upwards [hp] with v hv
    have hh := (kernel_strict hx hxy ha hv).le
    have he (z : ℝ) : f z v = (v-a)^2 * (z^3 / ((z+a)^2 * (z+v))) := by
      dsimp [f]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    rw [he, he]
    exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)
  apply lt_of_le_of_ne (integral_mono_ae (hi x hx) (hi y hy) hle)
  intro he
  have heq := (integral_eq_iff_of_ae_le (hi x hx) (hi y hy) hle).mp he
  have hz : (fun v => (v-a)^2) =ᵐ[M] 0 := by
    filter_upwards [hp, heq] with v hv heq
    have hh := kernel_strict hx hxy ha hv
    have he (z : ℝ) : f z v = (v-a)^2 * (z^3 / ((z+a)^2 * (z+v))) := by
      dsimp [f]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    rw [he, he] at heq
    dsimp
    nlinarith [sq_nonneg (v-a)]
  have hzint : (∫ v, (v-a)^2 ∂M) = 0 := by
    rw [integral_congr_ae hz]; simp
  linarith

end D5.S3.Analytic.WallisRemainder.Stieltjes
