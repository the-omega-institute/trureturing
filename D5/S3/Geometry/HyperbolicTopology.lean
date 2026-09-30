/- GID: D5/S3/Geometry/HyperbolicTopology
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.UpperHalfPlane.Metric]
   utility: none
   digest: Hyperbolic coordinate homeomorphism and compact closed balls over proper spaces. -/

import D5.S3.Geometry.HyperbolicCompleteness
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.HyperbolicTopology

open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicCompleteness
open Filter Topology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem continuous_coordinates :
    Continuous (fun p : HyperbolicSpace E => p.coordinates) := by
  have hl : LipschitzWith 1 (fun p : HyperbolicSpace E => Real.log (height p.coordinates)) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (Real.log (height p.coordinates)) (Real.log (height q.coordinates)) ≤
      1 * hyperbolicDist p.coordinates q.coordinates
    simpa only [one_mul] using dist_log_height_le p.coordinates q.coordinates
  have hh : Continuous (fun p : HyperbolicSpace E => height p.coordinates) :=
    (Real.continuous_exp.comp hl.continuous).congr
      (fun p => Real.exp_log p.coordinates.2)
  have hc : Continuous (fun p : HyperbolicSpace E => p.coordinates.1) := by
    rw [continuous_iff_continuousAt]
    intro p
    apply tendsto_iff_dist_tendsto_zero.2
    have hd : Tendsto (fun q : HyperbolicSpace E => dist q p) (𝓝 p) (𝓝 0) := by
      simpa using (continuous_id.dist (continuous_const (y := p))).tendsto p
    have hr : Tendsto
        (fun q : HyperbolicSpace E => 2 * √(height q.coordinates * height p.coordinates))
        (𝓝 p) (𝓝 (2 * √(height p.coordinates * height p.coordinates))) :=
      tendsto_const_nhds.mul (hh.continuousAt.tendsto.mul_const (height p.coordinates)).sqrt
    have hs := (Real.continuous_sinh.tendsto 0).comp (by simpa using hd.div_const 2)
    have heq (q : HyperbolicSpace E) :
        dist (q.coordinates.1 : Ambient E) p.coordinates.1 =
          2 * √(height q.coordinates * height p.coordinates) * Real.sinh (dist q p / 2) := by
      change dist (q.coordinates.1 : Ambient E) p.coordinates.1 =
        2 * √(height q.coordinates * height p.coordinates) *
          Real.sinh (hyperbolicDist q.coordinates p.coordinates / 2)
      rw [sinh_half_hyperbolicDist]
      have hp : √(height q.coordinates * height p.coordinates) ≠ 0 :=
        (Real.sqrt_pos.2 (mul_pos q.coordinates.2 p.coordinates.2)).ne'
      field_simp [hp]
    have ht : Tendsto
        (fun q : HyperbolicSpace E =>
          2 * √(height q.coordinates * height p.coordinates) * Real.sinh (dist q p / 2))
        (𝓝 p) (𝓝 0) := by simpa using hr.mul hs
    exact ht.congr (fun q => (heq q).symm)
  exact hc.subtype_mk (fun p => p.coordinates.2)

/-- The hyperbolic metric induces the usual positive-height coordinate topology. -/
noncomputable def coordinatesHomeomorph : HyperbolicSpace E ≃ₜ UpperHalfSpace E where
  toFun p := p.coordinates
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_coordinates
  continuous_invFun := by
    rw [continuous_iff_continuous_dist]
    change Continuous (fun z : UpperHalfSpace E × UpperHalfSpace E =>
      2 * Real.arsinh (dist (z.1.1 : Ambient E) z.2.1 /
        (2 * √(height z.1 * height z.2))))
    have hh : Continuous (height : UpperHalfSpace E → ℝ) :=
      (WithLp.continuous_snd 2 E ℝ).comp continuous_subtype_val
    have hn : Continuous (fun z : UpperHalfSpace E × UpperHalfSpace E =>
        dist (z.1.1 : Ambient E) z.2.1) :=
      (continuous_subtype_val.comp continuous_fst).dist
        (continuous_subtype_val.comp continuous_snd)
    have hd : Continuous (fun z : UpperHalfSpace E × UpperHalfSpace E =>
        2 * √(height z.1 * height z.2)) :=
      continuous_const.mul ((hh.comp continuous_fst).mul (hh.comp continuous_snd)).sqrt
    have hne (z : UpperHalfSpace E × UpperHalfSpace E) :
        2 * √(height z.1 * height z.2) ≠ 0 := by
      have h1 : 0 < height z.1 := z.1.2
      have h2 : 0 < height z.2 := z.2.2
      positivity
    exact continuous_const.mul (Real.continuous_arsinh.comp (hn.div hd hne))

/-- Hyperbolic closed balls are compact when the horizontal metric is proper. -/
noncomputable instance hyperbolicProperSpace [ProperSpace E] :
    ProperSpace (HyperbolicSpace E) := by
  apply ProperSpace.of_isCompact_closedBall_of_le 0
  intro p r hr
  let U := height p.coordinates * Real.exp r
  let L := height p.coordinates * Real.exp (-r)
  let R := 2 * U * Real.sinh (r / 2)
  have hU : 0 < U := mul_pos p.coordinates.2 (Real.exp_pos r)
  have hL : 0 < L := mul_pos p.coordinates.2 (Real.exp_pos (-r))
  have hpU : height p.coordinates ≤ U := by
    have hexp : 1 ≤ Real.exp r := by simpa using Real.exp_le_exp.mpr hr
    change height p.coordinates ≤ height p.coordinates * Real.exp r
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
      (show 0 ≤ height p.coordinates from p.coordinates.2.le)
  have hheight (q : HyperbolicSpace E) (hq : q ∈ closedBall p r) :
      height q.coordinates ∈ Icc L U := by
    have hd : hyperbolicDist q.coordinates p.coordinates ≤ r := hq
    have hlog := (dist_log_height_le q.coordinates p.coordinates).trans hd
    rw [Real.dist_eq] at hlog
    have hqp : 0 < height q.coordinates := q.coordinates.2
    have hpp : 0 < height p.coordinates := p.coordinates.2
    have hupper : height q.coordinates ≤ U := by
      have hs : Real.log (height q.coordinates) - Real.log (height p.coordinates) ≤ r :=
        (le_abs_self _).trans hlog
      have he := Real.exp_le_exp.mpr hs
      rw [Real.exp_sub, Real.exp_log hqp, Real.exp_log hpp] at he
      simpa [U, mul_comm] using (div_le_iff₀ hpp).mp he
    have hlower : L ≤ height q.coordinates := by
      have hs : -r ≤ Real.log (height q.coordinates) - Real.log (height p.coordinates) := by
        have hneg := neg_abs_le
          (Real.log (height q.coordinates) - Real.log (height p.coordinates))
        linarith
      have he := Real.exp_le_exp.mpr hs
      rw [Real.exp_sub, Real.exp_log hqp, Real.exp_log hpp] at he
      simpa [L, mul_comm] using (le_div_iff₀ hpp).mp he
    exact ⟨hlower, hupper⟩
  have hcoord (q : HyperbolicSpace E) (hq : q ∈ closedBall p r) :
      dist (q.coordinates.1 : Ambient E) p.coordinates.1 ≤ R := by
    have hqU := (hheight q hq).2
    have hs : √(height q.coordinates * height p.coordinates) ≤ U := by
      apply (Real.sqrt_le_left hU.le).2
      simpa only [sq] using mul_le_mul hqU hpU p.coordinates.2.le hU.le
    have hroot : √(height q.coordinates * height p.coordinates) ≠ 0 :=
      (Real.sqrt_pos.2 (mul_pos q.coordinates.2 p.coordinates.2)).ne'
    have heq : dist (q.coordinates.1 : Ambient E) p.coordinates.1 =
        2 * √(height q.coordinates * height p.coordinates) * Real.sinh (dist q p / 2) := by
      change dist (q.coordinates.1 : Ambient E) p.coordinates.1 =
        2 * √(height q.coordinates * height p.coordinates) *
          Real.sinh (hyperbolicDist q.coordinates p.coordinates / 2)
      rw [sinh_half_hyperbolicDist]
      field_simp [hroot]
    rw [heq]
    calc
      _ ≤ 2 * U * Real.sinh (dist q p / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sinh_nonneg_iff.2 (by positivity))
      _ ≤ R := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.sinh_le_sinh.mpr (div_le_div_of_nonneg_right hq (by norm_num))
  let K : Set (E × ℝ) := closedBall p.coordinates.1.fst R ×ˢ Icc L U
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K → HyperbolicSpace E := fun z =>
    ⟨⟨WithLp.toLp 2 z.1, hL.trans_le z.2.2.1⟩⟩
  have hF : Continuous F := by
    apply coordinatesHomeomorph.symm.continuous.comp
    exact ((WithLp.prod_continuous_toLp 2 E ℝ).comp continuous_subtype_val).subtype_mk
      (fun z => hL.trans_le z.2.2.1)
  have hcompact : IsCompact (range F) := by
    simpa only [image_univ] using isCompact_univ.image hF
  apply hcompact.of_isClosed_subset isClosed_closedBall
  intro q hq
  have hx : (q.coordinates.1.fst, height q.coordinates) ∈ K :=
    ⟨(WithLp.dist_fst_le q.coordinates.1 p.coordinates.1).trans (hcoord q hq), hheight q hq⟩
  refine ⟨⟨(q.coordinates.1.fst, height q.coordinates), hx⟩, ?_⟩
  apply congrArg HyperbolicSpace.mk
  apply Subtype.ext
  rfl

#print axioms coordinatesHomeomorph
#print axioms hyperbolicProperSpace

end D5.S3.Geometry.HyperbolicTopology
