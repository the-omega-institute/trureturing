/- GID: D5/S3/Geometry/HyperbolicHausdorffComparison
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicHausdorffComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Measure.Hausdorff]
   utility: none
   digest: Local Hausdorff measure distortion for the unchanged native hyperbolic metric. -/

import D5.S3.Geometry.HyperbolicUpperHalfSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped NNReal ENNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace D5.S3.Geometry.HyperbolicHausdorffComparison

private local instance : MeasurableSpace (UpperHalfSpace ℂ) := borel _
private local instance : BorelSpace (UpperHalfSpace ℂ) := ⟨rfl⟩
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

private theorem arsinh_bounds (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.arsinh x ∧ Real.arsinh x ≤ x := by
  have hpos : 0 < 1 + x := by positivity
  have hs : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith [sq_nonneg x]
  constructor
  · calc
      x / (1 + x) = 1 - (1 + x)⁻¹ := by field_simp; ring
      _ ≤ Real.log (1 + x) := Real.one_sub_inv_le_log_of_pos hpos
      _ ≤ Real.arsinh x := Real.log_le_log hpos (by linarith)
  · have ha : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr hx
    simpa only [Real.sinh_arsinh] using Real.self_le_sinh_iff.mpr ha

private theorem ball_distortion (p : UpperHalfSpace ℂ) (r : ℝ)
    (hr : 0 < r) (hrh : r < height p) (u v : UpperHalfSpace ℂ)
    (hu : dist u p < r) (hv : dist v p < r) :
    dist u v ≤ (height p + 2 * r) *
      dist (HyperbolicSpace.mk u) (HyperbolicSpace.mk v) ∧
    dist (HyperbolicSpace.mk u) (HyperbolicSpace.mk v) ≤
      (height p - r)⁻¹ * dist u v := by
  let h := height p
  let D := dist u v
  let a := Real.sqrt (height u * height v)
  have hp : 0 < h := p.property
  have hlow : 0 < h - r := sub_pos.mpr hrh
  have hh (w : UpperHalfSpace ℂ) (hw : dist w p < r) :
      h - r ≤ height w ∧ height w ≤ h + r := by
    have hd : |height w - height p| ≤ dist w p :=
      WithLp.dist_snd_le w.val p.val
    have he := abs_le.mp (hd.trans hw.le)
    dsimp [h]
    constructor <;> linarith
  have hhu := hh u hu
  have hhv := hh v hv
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos u.property v.property)
  have haLow : h - r ≤ a := by
    apply (Real.le_sqrt hlow.le (mul_pos u.property v.property).le).2
    calc
      (h-r)^2 = (h-r)*(h-r) := sq _
      _ ≤ height u * height v := mul_le_mul hhu.1 hhv.1 hlow.le u.property.le
  have haHigh : a ≤ h + r := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ h + r)).2
    simpa only [sq] using mul_le_mul hhu.2 hhv.2 v.property.le (by positivity : 0 ≤ h+r)
  have hD : 0 ≤ D := dist_nonneg
  have hDhigh : D ≤ 2 * r := by
    have ht := dist_triangle u p v
    rw [dist_comm p v] at ht
    dsimp [D]
    linarith
  have hb := arsinh_bounds (D / (2*a)) (by positivity)
  have heq : dist (HyperbolicSpace.mk u) (HyperbolicSpace.mk v) =
      2 * Real.arsinh (D / (2*a)) := rfl
  rw [heq]
  have hden : 0 < 2*a + D := by positivity
  have hfract : (D/(2*a))/(1+D/(2*a)) = D/(2*a+D) := by
    field_simp
  rw [hfract] at hb
  constructor
  · have hmul : D ≤ Real.arsinh (D/(2*a)) * (2*a+D) :=
      (div_le_iff₀ hden).mp hb.1
    have hnon : 0 ≤ Real.arsinh (D/(2*a)) :=
      Real.arsinh_nonneg_iff.mpr (by positivity)
    nlinarith [mul_nonneg hnon (show 0 ≤ 2*(h+2*r)-(2*a+D) by linarith)]
  · calc
      2 * Real.arsinh (D/(2*a)) ≤ 2 * (D/(2*a)) := by linarith [hb.2]
      _ = D/a := by field_simp
      _ ≤ D/(h-r) := div_le_div_of_nonneg_left hD hlow haLow
      _ = (h-r)⁻¹ * D := by ring

/-- For every subset of a Euclidean coordinate ball of radius `r < height p`,
raw three-dimensional Hausdorff measure in the original hyperbolic metric is
bounded above and below by explicit Euclidean Hausdorff multiples. No
measurability, distinct-point, frame, or volume-identification hypothesis is used. -/
theorem local_hausdorff_comparison (p : UpperHalfSpace ℂ) (r : ℝ)
    (hr : 0 < r) (hrh : r < height p) (s : Set (UpperHalfSpace ℂ))
    (hs : s ⊆ Metric.ball p r) :
    Measure.hausdorffMeasure 3 s ≤
      (ENNReal.ofReal (height p + 2*r)) ^ (3 : ℝ) *
        Measure.hausdorffMeasure 3 (HyperbolicSpace.mk '' s) ∧
    Measure.hausdorffMeasure 3 (HyperbolicSpace.mk '' s) ≤
      (ENNReal.ofReal ((height p-r)⁻¹)) ^ (3 : ℝ) *
        Measure.hausdorffMeasure 3 s := by
  let K : ℝ≥0 := ⟨height p + 2*r,
    (add_pos p.property (mul_pos (by norm_num) hr)).le⟩
  let J : ℝ≥0 := ⟨(height p-r)⁻¹, inv_nonneg.mpr (sub_pos.mpr hrh).le⟩
  have forward : LipschitzOnWith J (HyperbolicSpace.mk (E := ℂ)) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    exact (ball_distortion p r hr hrh u v (hs hu) (hs hv)).2
  have backward : LipschitzOnWith K HyperbolicSpace.coordinates
      (HyperbolicSpace.mk '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (ball_distortion p r hr hrh u v (hs hu) (hs hv)).1
  have himage : HyperbolicSpace.coordinates '' (HyperbolicSpace.mk '' s) = s := by
    rw [← Set.image_comp]
    exact Set.image_id s
  constructor
  · have hb := backward.hausdorffMeasure_image_le (d := 3) (by norm_num)
    rw [himage] at hb
    have hK : (K : ℝ≥0∞) = ENNReal.ofReal (height p + 2*r) :=
      ENNReal.coe_nnreal_eq K
    rw [hK] at hb
    exact hb
  · have hf := forward.hausdorffMeasure_image_le (d := 3) (by norm_num)
    have hJ : (J : ℝ≥0∞) = ENNReal.ofReal ((height p-r)⁻¹) :=
      ENNReal.coe_nnreal_eq J
    rw [hJ] at hf
    exact hf

#print axioms local_hausdorff_comparison
end D5.S3.Geometry.HyperbolicHausdorffComparison
