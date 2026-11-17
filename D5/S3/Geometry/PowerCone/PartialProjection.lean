/- GID: D5/S3/Geometry/PowerCone/PartialProjection
   generality: I
   mirror-B: D5/B/S3/Geometry/PowerCone/PartialProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Geometry.PowerCone.Topology
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
The concrete geometry needed for partial minimization in the scalar power cone.
The partial-minimization argument is Zhang--Fu--Dai, arXiv:2611.06404v1,
Lemma 3.1 and the beginning of the proof of Theorem 3.5, printed pp. 6, 9.
These are uncompiled proof sources, not a kernel receipt.
-/

open Set Filter
open scoped Topology

namespace D5.S3.Geometry.PowerCone

def quadrant : Set (ℝ × ℝ) := {u | 0 < u.1 ∧ 0 < u.2}
def closedQuadrant : Set (ℝ × ℝ) := {u | 0 ≤ u.1 ∧ 0 ≤ u.2}
def quadrantBoundary : Set (ℝ × ℝ) := closedQuadrant \ quadrant

theorem quadrant_isOpen : IsOpen quadrant :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd)

theorem closedQuadrant_isClosed : IsClosed closedQuadrant :=
  (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const continuous_snd)

theorem quadrant_eq_interior : quadrant = interior closedQuadrant := by
  apply Subset.antisymm
  · exact interior_maximal (fun _ h => ⟨h.1.le,h.2.le⟩) quadrant_isOpen
  · intro u hu
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hu)
    have he : 0 < ε/2 := half_pos hε
    have hx := hball (show (u.1-ε/2,u.2) ∈ Metric.ball u ε by
      rw [Metric.mem_ball]
      have h : u.1-ε/2-u.1 = -(ε/2) := by ring
      have hd : dist (u.1-ε/2,u.2) u = ε/2 := by
        simp only [Prod.dist_eq, Real.dist_eq, h, abs_neg, abs_of_pos he,
          sub_self, abs_zero]
        exact max_eq_left he.le
      rw [hd]
      linarith)
    have hy := hball (show (u.1,u.2-ε/2) ∈ Metric.ball u ε by
      rw [Metric.mem_ball]
      have h : u.2-ε/2-u.2 = -(ε/2) := by ring
      have hd : dist (u.1,u.2-ε/2) u = ε/2 := by
        simp only [Prod.dist_eq, Real.dist_eq, h, abs_neg, abs_of_pos he,
          sub_self, abs_zero]
        exact max_eq_right he.le
      rw [hd]
      linarith)
    exact ⟨by have := hx.1; linarith,by have := hy.2; linarith⟩

theorem quadrantBoundary_eq_frontier : quadrantBoundary = frontier closedQuadrant := by
  simp only [quadrantBoundary,closedQuadrant_isClosed.frontier_eq,← quadrant_eq_interior]

theorem weight_pos {c : ℝ} {u : ℝ × ℝ} (hu : u ∈ quadrant) :
    0 < weight c u.1 u.2 :=
  mul_pos (Real.rpow_pos_of_pos hu.1 _) (Real.rpow_pos_of_pos hu.2 _)

theorem scalar_fiber_eq {c : ℝ} {u : ℝ × ℝ} (hu : u ∈ quadrant) :
    {z : ℝ | (u,z) ∈ coneInterior c} =
      Ioo (-weight c u.1 u.2) (weight c u.1 u.2) := by
  ext z
  simp only [mem_setOf_eq, coneInterior, Real.norm_eq_abs, mem_Ioo]
  exact ⟨fun h => abs_lt.mp h.2.2, fun h => ⟨hu.1, hu.2, abs_lt.mpr h⟩⟩

theorem scalar_mem_fiber_iff {c : ℝ} {u : ℝ × ℝ} (hu : u ∈ quadrant) (z : ℝ) :
    (u,z) ∈ coneInterior c ↔
      z ∈ Ioo (-weight c u.1 u.2) (weight c u.1 u.2) := by
  change z ∈ {z : ℝ | (u,z) ∈ coneInterior c} ↔ _
  rw [scalar_fiber_eq hu]

theorem project_interior (c : ℝ) :
    Prod.fst '' (coneInterior c : Set (Point ℝ)) = quadrant := by
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp.1, hp.2.1⟩
  · intro hu
    refine ⟨(u,0), ⟨hu.1,hu.2,?_⟩, rfl⟩
    simpa using weight_pos (c := c) hu

theorem project_closed (c : ℝ) :
    Prod.fst '' (closedCone c : Set (Point ℝ)) = closedQuadrant := by
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp.1,hp.2.1⟩
  · intro hu
    refine ⟨(u,0), ⟨hu.1,hu.2,?_⟩, rfl⟩
    simpa [weight] using mul_nonneg
      (Real.rpow_nonneg hu.1 c) (Real.rpow_nonneg hu.2 (1-c))

theorem project_actual_interior {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Prod.fst '' interior (closedCone c : Set (Point ℝ)) =
      interior (Prod.fst '' (closedCone c : Set (Point ℝ))) := by
  rw [← coneInterior_eq_interior hc.le hc1.le,project_interior,project_closed,
    ← quadrant_eq_interior]

theorem quadrantBoundary_coordinates {u : ℝ × ℝ} (hu : u ∈ quadrantBoundary) :
    0 ≤ u.1 ∧ 0 ≤ u.2 ∧ (u.1 = 0 ∨ u.2 = 0) := by
  refine ⟨hu.1.1,hu.1.2,?_⟩
  by_contra h
  push_neg at h
  exact hu.2 ⟨lt_of_le_of_ne hu.1.1 (Ne.symm h.1),
    lt_of_le_of_ne hu.1.2 (Ne.symm h.2)⟩

theorem weight_eq_zero_at_quadrantBoundary {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {u : ℝ × ℝ} (hu : u ∈ quadrantBoundary) : weight c u.1 u.2 = 0 := by
  obtain ⟨_,_,h⟩ := quadrantBoundary_coordinates hu
  rcases h with h | h
  · simp [weight,h,Real.zero_rpow hc.ne']
  · simp [weight,h,Real.zero_rpow (sub_pos.mpr hc1).ne']

theorem quadrantBoundary_lift {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {u : ℝ × ℝ} (hu : u ∈ quadrantBoundary) :
    (u,(0:ℝ)) ∈ coneBoundary c := by
  refine ⟨⟨hu.1.1,hu.1.2,?_⟩,?_⟩
  · simp [weight_eq_zero_at_quadrantBoundary hc hc1 hu]
  · intro hp
    exact hu.2 ⟨hp.1,hp.2.1⟩

theorem scalar_fiber_endpoints_boundary {c : ℝ} {u : ℝ × ℝ}
    (hu : u ∈ quadrant) :
    (u,-weight c u.1 u.2) ∈ coneBoundary c ∧
      (u,weight c u.1 u.2) ∈ coneBoundary c := by
  have hw := weight_pos (c := c) hu
  constructor
  · refine ⟨⟨hu.1.le,hu.2.le,?_⟩,?_⟩
    · simp [Real.norm_eq_abs,abs_of_pos hw]
    · intro hp
      have hz := hp.2.2
      simpa [Real.norm_eq_abs,abs_of_pos hw] using hz
  · refine ⟨⟨hu.1.le,hu.2.le,?_⟩,?_⟩
    · simp [Real.norm_eq_abs,abs_of_pos hw]
    · intro hp
      have hz := hp.2.2
      simpa [Real.norm_eq_abs,abs_of_pos hw] using hz

/-- No continuity or minimality of the selected fiber point is assumed here.
Every feasible selection collapses to zero over every finite projected boundary.
-/
theorem feasible_lift_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {u : ℕ → ℝ × ℝ} {z : ℕ → ℝ} {b : ℝ × ℝ}
    (hb : b ∈ quadrantBoundary) (hu : Tendsto u atTop (𝓝 b))
    (hz : ∀ n, (u n,z n) ∈ coneInterior c) :
    Tendsto (fun n => (u n,z n)) atTop (𝓝 (b,0)) := by
  have hw : Tendsto (fun n => weight c (u n).1 (u n).2) atTop (𝓝 0) := by
    have h := (((Real.continuous_rpow_const hc.le).tendsto b.1).comp hu.fst_nhds).mul
      (((Real.continuous_rpow_const (sub_pos.mpr hc1).le).tendsto b.2).comp hu.snd_nhds)
    have hzero : b.1^c * b.2^(1-c) = 0 := weight_eq_zero_at_quadrantBoundary hc hc1 hb
    simpa only [Function.comp_apply, weight, hzero] using h
  have hnorm : Tendsto (fun n => ‖z n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (hz n).2.2.le) hw
  have hzero : Tendsto z atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  exact hu.prodMk_nhds hzero

theorem weight_smul {c t : ℝ} (ht : 0 < t) {u : ℝ × ℝ}
    (hu : u ∈ quadrant) :
    weight c (t*u.1) (t*u.2) = t * weight c u.1 u.2 := by
  unfold weight
  rw [Real.mul_rpow ht.le hu.1.le,Real.mul_rpow ht.le hu.2.le]
  calc
    (t^c*u.1^c)*(t^(1-c)*u.2^(1-c)) =
        (t^c*t^(1-c))*(u.1^c*u.2^(1-c)) := by ring
    _ = t*(u.1^c*u.2^(1-c)) := by
      have he : c+(1-c) = (1:ℝ) := by ring
      rw [← Real.rpow_add ht,he,Real.rpow_one]

theorem scalar_fiber_smul {c t : ℝ} (ht : 0 < t) {u : ℝ × ℝ}
    (hu : u ∈ quadrant) (z : ℝ) :
    (t • u,t*z) ∈ coneInterior c ↔ (u,z) ∈ coneInterior c := by
  simp only [coneInterior,mem_setOf_eq,Prod.smul_def,smul_eq_mul,
    Real.norm_eq_abs,abs_mul,abs_of_pos ht,weight_smul ht hu]
  constructor
  · intro h
    exact ⟨hu.1,hu.2,(mul_lt_mul_iff_of_pos_left ht).mp h.2.2⟩
  · intro h
    exact ⟨mul_pos ht hu.1,mul_pos ht hu.2,mul_lt_mul_of_pos_left h.2.2 ht⟩

end D5.S3.Geometry.PowerCone
