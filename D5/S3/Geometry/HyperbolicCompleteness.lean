/- GID: D5/S3/Geometry/HyperbolicCompleteness
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.UpperHalfPlane.Metric]
   utility: none
   digest: Complete horizontal inner product spaces give complete hyperbolic upper half-spaces. -/

import D5.S3.Geometry.HyperbolicUpperHalfSpace
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.HyperbolicCompleteness

open D5.S3.Geometry.HyperbolicUpperHalfSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Logarithmic height varies by at most the hyperbolic distance. -/
theorem dist_log_height_le (p q : UpperHalfSpace E) :
    dist (Real.log (height p)) (Real.log (height q)) ≤ hyperbolicDist p q := by
  let z : UpperHalfPlane := UpperHalfPlane.mk ⟨0, height p⟩ p.2
  let w : UpperHalfPlane := UpperHalfPlane.mk ⟨0, height q⟩ q.2
  have hv : dist z w = dist (Real.log (height p)) (Real.log (height q)) :=
    UpperHalfPlane.dist_of_re_eq rfl
  rw [← hv, UpperHalfPlane.dist_eq, hyperbolicDist]
  dsimp [z, w]
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.arsinh_le_arsinh.mpr
  apply (div_le_div_iff_of_pos_right
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos p.2 q.2)))).2
  calc
    dist (⟨0, height p⟩ : ℂ) ⟨0, height q⟩ = dist (height p) (height q) :=
      Complex.dist_of_re_eq rfl
    _ ≤ dist (p.1 : Ambient E) q.1 := WithLp.dist_snd_le p.1 q.1

omit [InnerProductSpace ℝ E] in
private theorem height_le_mul_exp_dist (p q : UpperHalfSpace E) :
    height p ≤ height q * Real.exp (hyperbolicDist p q) := by
  have hp : 0 < height p := p.2
  have hq : 0 < height q := q.2
  rw [← div_le_iff₀' hq, ← Real.exp_log hp, ← Real.exp_log hq,
    ← Real.exp_sub, Real.exp_le_exp]
  exact (le_abs_self _).trans (dist_log_height_le p q)

private theorem dist_coordinates_le (p q : UpperHalfSpace E) (B : ℝ)
    (hB : 0 < B) (hp : height p ≤ B) (hq : height q ≤ B) :
    dist (p.1 : Ambient E) q.1 ≤ 2 * B * Real.sinh (hyperbolicDist p q / 2) := by
  have hs : √(height p * height q) ≤ B := by
    apply (Real.sqrt_le_left hB.le).2
    simpa [sq] using mul_le_mul hp hq q.2.le hB.le
  have hroot : 0 < √(height p * height q) := Real.sqrt_pos.2 (mul_pos p.2 q.2)
  have heq : dist (p.1 : Ambient E) q.1 =
      2 * √(height p * height q) * Real.sinh (hyperbolicDist p q / 2) := by
    rw [sinh_half_hyperbolicDist]
    field_simp [hroot.ne']
  rw [heq]
  apply mul_le_mul_of_nonneg_right (by linarith)
  apply Real.sinh_nonneg_iff.2
  have hd : 0 ≤ dist (⟨p⟩ : HyperbolicSpace E) ⟨q⟩ := dist_nonneg
  exact div_nonneg hd (by norm_num)

private theorem cauchySeq_coordinates (u : ℕ → HyperbolicSpace E) (hu : CauchySeq u) :
    CauchySeq (fun n => (u n).coordinates.1) := by
  obtain ⟨R, _, hR⟩ := cauchySeq_bdd hu
  let B := height (u 0).coordinates * Real.exp R
  have hB : 0 < B := mul_pos (u 0).coordinates.2 (Real.exp_pos R)
  have hheight (n : ℕ) : height (u n).coordinates ≤ B := by
    calc
      _ ≤ height (u 0).coordinates * Real.exp (hyperbolicDist (u n).coordinates
          (u 0).coordinates) := height_le_mul_exp_dist _ _
      _ ≤ B := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (hR n 0).le) (u 0).coordinates.2.le
  obtain ⟨b, _, hb, hbt⟩ := cauchySeq_iff_le_tendsto_0.mp hu
  refine cauchySeq_of_le_tendsto_0 (fun n => 2 * B * Real.sinh (b n / 2)) ?_ ?_
  · intro n m N hn hm
    calc
      _ ≤ 2 * B * Real.sinh (hyperbolicDist (u n).coordinates (u m).coordinates / 2) :=
        dist_coordinates_le _ _ B hB (hheight n) (hheight m)
      _ ≤ 2 * B * Real.sinh (b N / 2) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.sinh_le_sinh.mpr
          ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 (hb n m N hn hm))
  · have hsinh := (Real.continuous_sinh.tendsto 0).comp (by simpa using hbt.div_const 2)
    simpa using tendsto_const_nhds.mul hsinh

/-- Hyperbolic Cauchy sequences converge when the horizontal space is complete. -/
noncomputable instance hyperbolicCompleteSpace [CompleteSpace E] :
    CompleteSpace (HyperbolicSpace E) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hlog : CauchySeq (fun n => Real.log (height (u n).coordinates)) := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    exact ⟨N, fun m hm n hn => (dist_log_height_le _ _).trans_lt (hN m hm n hn)⟩
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hlog
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (cauchySeq_coordinates u hu)
  have hheight : Tendsto (fun n => height (u n).coordinates) atTop (𝓝 (Real.exp a)) := by
    have he := (Real.continuous_exp.tendsto a).comp ha
    have heq (n : ℕ) : Real.exp (Real.log (height (u n).coordinates)) =
        height (u n).coordinates := Real.exp_log (u n).coordinates.2
    simpa only [Function.comp_def, heq] using he
  have hcoordheight : Tendsto (fun n => height (u n).coordinates) atTop (𝓝 z.snd) :=
    ((WithLp.continuous_snd (p := 2) (α := E) (β := ℝ)).tendsto z).comp hz
  have hzeq : z.snd = Real.exp a := tendsto_nhds_unique hcoordheight hheight
  have hpos : 0 < z.snd := hzeq ▸ Real.exp_pos a
  let p : HyperbolicSpace E := ⟨⟨z, hpos⟩⟩
  refine ⟨p, tendsto_iff_dist_tendsto_zero.2 ?_⟩
  have hdist : Tendsto (fun n => dist ((u n).coordinates.1 : Ambient E) z) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hz
  have hroot : Tendsto (fun n => 2 * √(height (u n).coordinates * z.snd))
      atTop (𝓝 (2 * √(z.snd * z.snd))) :=
    tendsto_const_nhds.mul (hcoordheight.mul_const z.snd).sqrt
  have hrootne : 2 * √(z.snd * z.snd) ≠ 0 := by positivity
  have hratio := hdist.div hroot hrootne
  have harsinh := (Real.continuous_arsinh.tendsto 0).comp (by simpa using hratio)
  change Tendsto (fun n => hyperbolicDist (u n).coordinates p.coordinates) atTop (𝓝 0)
  simpa [p, hyperbolicDist, height] using
    (tendsto_const_nhds.mul harsinh : Tendsto
      (fun n => 2 * Real.arsinh (dist ((u n).coordinates.1 : Ambient E) z /
        (2 * √(height (u n).coordinates * z.snd)))) atTop (𝓝 (2 * Real.arsinh 0)))

#print axioms dist_log_height_le
#print axioms hyperbolicCompleteSpace

end D5.S3.Geometry.HyperbolicCompleteness
