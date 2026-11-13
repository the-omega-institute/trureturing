/- GID: D5/S3/Geometry/PowerCone/Topology
   generality: I
   mirror-B: D5/B/S3/Geometry/PowerCone/Topology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Geometry.PowerCone.ScalarSection
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
Topological identification of the explicit domain/boundary.  This completes
the finite-boundary part of the scalar restriction at the level of source.
No convexity/regular-cone theorem or scalar parameter theorem is inferred.
Source only; no elaboration/kernel check has run.
-/

open Set
open D5.S3.Analytic.ConvexBarrier

namespace D5.S3.Geometry.PowerCone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem weight_continuous {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    Continuous (fun p : Point V => weight c p.1.1 p.1.2) := by
  exact ((Real.continuous_rpow_const hc).comp (by fun_prop)).mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ 1-c)).comp (by fun_prop))

theorem closedCone_isClosed {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    IsClosed (closedCone c : Set (Point V)) := by
  change IsClosed ({p : Point V | 0 ≤ p.1.1} ∩
    ({p | 0 ≤ p.1.2} ∩ {p | ‖p.2‖ ≤ weight c p.1.1 p.1.2}))
  exact (isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) (weight_continuous hc hc1)))

theorem coneInterior_isOpen {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    IsOpen (coneInterior c : Set (Point V)) := by
  change IsOpen ({p : Point V | 0 < p.1.1} ∩
    ({p | 0 < p.1.2} ∩ {p | ‖p.2‖ < weight c p.1.1 p.1.2}))
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (weight_continuous hc hc1)))

theorem coneInterior_eq_interior {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (coneInterior c : Set (Point V)) = interior (closedCone c) := by
  apply Subset.antisymm
  · apply interior_maximal _ (coneInterior_isOpen hc hc1)
    exact fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  · intro p hp
    have hpK : p ∈ closedCone c := interior_subset hp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
    have hhalf : 0 < ε/2 := half_pos hε
    have hxDist : dist (((p.1.1-ε/2,p.1.2),p.2) : Point V) p = ε/2 := by
      have he : p.1.1-ε/2-p.1.1 = -(ε/2) := by ring
      simp [Prod.dist_eq, Real.dist_eq, he, abs_of_pos hε, hhalf.le]
    have hyDist : dist (((p.1.1,p.1.2-ε/2),p.2) : Point V) p = ε/2 := by
      have he : p.1.2-ε/2-p.1.2 = -(ε/2) := by ring
      simp [Prod.dist_eq, Real.dist_eq, he, abs_of_pos hε, hhalf.le]
    have hxK := hball (show ((p.1.1-ε/2,p.1.2),p.2) ∈ Metric.ball p ε by
      rw [Metric.mem_ball, hxDist]; linarith)
    have hyK := hball (show ((p.1.1,p.1.2-ε/2),p.2) ∈ Metric.ball p ε by
      rw [Metric.mem_ball, hyDist]; linarith)
    have hx : 0 < p.1.1 := by have := hxK.1; linarith
    have hy : 0 < p.1.2 := by have := hyK.2.1; linarith
    refine ⟨hx, hy, ?_⟩
    have hw : 0 < weight c p.1.1 p.1.2 :=
      mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)
    by_contra hn
    have heq : ‖p.2‖ = weight c p.1.1 p.1.2 := le_antisymm hpK.2.2 (le_of_not_gt hn)
    have hz : 0 < ‖p.2‖ := by rw [heq]; exact hw
    let t : ℝ := ε/(2*‖p.2‖)
    have ht : 0 < t := div_pos hε (by positivity)
    have htn : t*‖p.2‖ = ε/2 := by dsimp [t]; field_simp [hz.ne'] <;> ring
    have hzDist : dist ((p.1,(1+t) • p.2) : Point V) p = ε/2 := by
      rw [Prod.dist_eq]
      simp only [dist_self, max_eq_right (dist_nonneg : 0 ≤ dist ((1+t) • p.2) p.2)]
      rw [dist_eq_norm]
      have hv : (1+t) • p.2 - p.2 = t • p.2 := by
        rw [add_smul, one_smul, add_sub_cancel_left]
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos ht, htn]
    have hK := hball (show (p.1,(1+t) • p.2) ∈ Metric.ball p ε by
      rw [Metric.mem_ball, hzDist]; linarith)
    have hnorm := hK.2.2
    change ‖(1+t) • p.2‖ ≤ weight c p.1.1 p.1.2 at hnorm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1+t)] at hnorm
    nlinarith [mul_pos ht hz]

theorem coneBoundary_eq_frontier {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (coneBoundary c : Set (Point V)) = frontier (closedCone c) := by
  rw [(closedCone_isClosed hc hc1).frontier_eq, ← coneInterior_eq_interior hc hc1]
  rfl

/-- Restriction on the actual topological cone interiors and frontiers.
In particular no finite-boundary hypothesis is left for the user to supply. -/
theorem restrict_actual_cone {c ν : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {v : V} (hv : ‖v‖ = 1) {F : Point V → ℝ}
    (hF : IsLHSCB ν (interior (closedCone c)) (frontier (closedCone c)) F) :
    IsLHSCB ν (interior (closedCone c : Set (Point ℝ)))
      (frontier (closedCone c : Set (Point ℝ))) (F ∘ scalarSection v) := by
  rw [← coneInterior_eq_interior hc.le hc1.le,
    ← coneBoundary_eq_frontier hc.le hc1.le] at hF ⊢
  exact restrict_to_scalar hv hF

end D5.S3.Geometry.PowerCone
