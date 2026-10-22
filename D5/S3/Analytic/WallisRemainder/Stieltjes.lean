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

/-- The resolvent is integrable against a positive probability law. -/
theorem integrable_resolvent {M : Measure ℝ} [IsProbabilityMeasure M]
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

private lemma stieltjes_le {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v) {z : ℝ} (hz : 0 < z) :
    stieltjes M z ≤ 1 / z := by
  have hh : (fun v : ℝ => 1 / (z+v)) ≤ᵐ[M] (fun _ => 1/z) := by
    filter_upwards [hp] with v hv
    exact one_div_le_one_div_of_le hz (by linarith)
  simpa [stieltjes] using integral_mono_ae (integrable_resolvent hp hz)
    (integrable_const (1/z)) hh

private lemma reciprocal_remainder {x y q v : ℝ} (hx : 0 < x) (hxy : x < y)
    (hv : 0 < v) (ht : 0 < 1-(y-x)*q) :
    1/(x+v) - q/(1-(y-x)*q) -
      (1/(y+v)-q)/(1-(y-x)*q)^2 =
    (y-x) * (1/(y+v)-q)^2 * (y+v) /
      ((x+v)*(1-(y-x)*q)^2) := by
  have h1 : x+v ≠ 0 := ne_of_gt (by linarith)
  have h2 : y+v ≠ 0 := ne_of_gt (by linarith)
  generalize he : 1-(y-x)*q = t at ht ⊢
  field_simp [h1, h2, ht.ne']
  rw [← he]
  ring

/-- The reciprocal Stieltjes transform minus its argument is strictly increasing. -/
theorem strictMonoOn_inv_stieltjes_sub {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v)
    (hnd : ∀ a : ℝ, ¬ ∀ᵐ v ∂M, v = a) :
    StrictMonoOn (fun z => 1 / stieltjes M z - z) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have hd : 0 < y-x := sub_pos.mpr hxy
  let q := stieltjes M y
  let t := 1-(y-x)*q
  have hq : 0 < q := stieltjes_pos hp hy
  have ht : 0 < t := by
    have hh := stieltjes_le hp hy
    have hqy : q*y ≤ 1 := (le_div_iff₀ hy).mp hh
    dsimp [t]
    nlinarith [mul_pos hx hq]
  let f : ℝ → ℝ := fun v =>
    1/(x+v) - q/t - (1/(y+v)-q)/t^2
  have hix : Integrable (fun v : ℝ => 1/(x+v)-q/t) M :=
    (integrable_resolvent hp hx).sub (integrable_const (q/t))
  have hiy : Integrable (fun v : ℝ => (1/(y+v)-q)/t^2) M :=
    ((integrable_resolvent hp hy).sub (integrable_const q)).div_const (t^2)
  have hfi : Integrable f M := hix.sub hiy
  have hid (v : ℝ) (hv : 0 < v) :
      f v = (y-x)*(1/(y+v)-q)^2*(y+v)/((x+v)*t^2) :=
    reciprocal_remainder hx hxy hv ht
  have hnn : ∀ᵐ v ∂M, 0 ≤ f v := by
    filter_upwards [hp] with v hv
    rw [hid v hv]
    have hyv : 0 < y+v := by linarith
    have hxv : 0 < x+v := by linarith
    positivity
  have hpos : 0 < ∫ v, f v ∂M := by
    apply integral_pos_of_not_zero hfi hnn
    intro he
    apply hnd (1/q-y)
    filter_upwards [hp, he] with v hv he
    have he' : 1/(y+v)=q := by
      by_contra hne
      have hh : 0 < f v := by
        rw [hid v hv]
        have hh : 0 < (1/(y+v)-q)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
        have hyv : 0 < y+v := by linarith
        have hxv : 0 < x+v := by linarith
        positivity
      exact hh.ne' he
    have hyvn : y+v ≠ 0 := ne_of_gt (by linarith)
    have hqv : q*(y+v)=1 := by rw [← he']; field_simp
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff hq.ne').mpr
    nlinarith
  have hint : (∫ v, f v ∂M) = stieltjes M x - q/t := by
    dsimp [f]
    rw [integral_sub hix hiy,
      integral_sub (f := fun v : ℝ => 1/(x+v)) (g := fun _ => q/t)
        (integrable_resolvent hp hx) (integrable_const (q/t)),
      integral_div (f := fun v : ℝ => 1/(y+v)-q),
      integral_sub (f := fun v : ℝ => 1/(y+v)) (g := fun _ => q)
        (integrable_resolvent hp hy) (integrable_const q)]
    simp [q, stieltjes]
  rw [hint] at hpos
  have hsx : 0 < stieltjes M x := stieltjes_pos hp hx
  have hmain : q < stieltjes M x * t := (div_lt_iff₀ ht).mp (sub_pos.mp hpos)
  have hh : (1+(y-x)*stieltjes M x) / stieltjes M x < 1/q := by
    apply (div_lt_div_iff₀ hsx hq).mpr
    dsimp [t] at hmain
    nlinarith
  have he : (1+(y-x)*stieltjes M x) / stieltjes M x =
      1/stieltjes M x + (y-x) := by field_simp
  rw [he] at hh
  change 1/stieltjes M x - x < 1/q-y
  linarith

/-- A positive probability law has a strictly positive, strictly subunit resolvent mass. -/
theorem stieltjes_bounds {M : Measure ℝ} [IsProbabilityMeasure M]
    (hp : ∀ᵐ v ∂M, 0 < v) {z : ℝ} (hz : 0 < z) :
    0 < stieltjes M z ∧ z * stieltjes M z < 1 := by
  refine ⟨stieltjes_pos hp hz, ?_⟩
  have hi : Integrable (fun v : ℝ => 1/z-1/(z+v)) M :=
    (integrable_const (1/z)).sub (integrable_resolvent hp hz)
  have hh (v : ℝ) (hv : 0 < v) : 0 < 1/z-1/(z+v) := by
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hz (by linarith))
  have hpos : 0 < ∫ v, (1/z-1/(z+v)) ∂M := by
    apply integral_pos_of_not_zero hi
    · filter_upwards [hp] with v hv using (hh v hv).le
    · intro he
      have hf : ∀ᵐ v ∂M, False := by
        filter_upwards [hp, he] with v hv he using (hh v hv).ne' he
      have he : M = 0 := by simpa using hf
      have ht : M Set.univ = 1 := measure_univ
      simp [he] at ht
  rw [integral_sub (f := fun _ : ℝ => 1/z) (g := fun v => 1/(z+v))
    (integrable_const (1/z)) (integrable_resolvent hp hz)] at hpos
  simp only [integral_const, probReal_univ, one_smul] at hpos
  have hh := (lt_div_iff₀ hz).mp (sub_pos.mp hpos)
  simpa [stieltjes, mul_comm] using hh

end D5.S3.Analytic.WallisRemainder.Stieltjes
