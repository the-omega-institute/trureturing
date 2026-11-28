/- GID: D5/S3/Combinatorics/Graph/SU2TangentFitClosure
   generality: G
   mirror-B: none(waiver:covered-by-su2-tangent-lower-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite-dimensional graph fitting by closed-range minimization. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

compile_only_with_mathlib

/-! Omega original.

Exact finite-dimensional graph fitting by closed-range minimization. -/

noncomputable section

namespace SimpleGraph

variable {V E : Type*} [Finite V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite-dimensional finite-graph fit has a minimizer. Consequently arbitrary
positive slack can be removed, without a boundedness assumption on the potentials. -/
theorem exists_gain_fit_of_forall_pos (G : SimpleGraph V) (g : V → V → E) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ η : ℝ, 0 < η → ∃ p : V → E,
      ∀ u v, G.Adj u v → ‖g u v - (p v - p u)‖ ≤ C + η) :
    ∃ p : V → E, ∀ u v, G.Adj u v → ‖g u v - (p v - p u)‖ ≤ C := by
  classical
  let := Fintype.ofFinite V
  let I := {e : V × V // G.Adj e.1 e.2}
  let a : I → E := fun e => g e.val.1 e.val.2
  let d : (V → E) →ₗ[ℝ] (I → E) :=
    { toFun := fun p e => p e.val.2 - p e.val.1
      map_add' := by intro p q; ext e; simp; abel
      map_smul' := by intro c p; ext e; simp [smul_sub] }
  obtain ⟨b, hb, heq⟩ := d.range.closed_of_finiteDimensional.exists_infDist_eq_dist
    (show (d.range : Set (I → E)).Nonempty from ⟨0, d.range.zero_mem⟩) a
  obtain ⟨p, rfl⟩ := hb
  have hd : dist a (d p) ≤ C := by
    rw [← heq]
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨q, hq⟩ := h η hη
    exact (Metric.infDist_le_dist_of_mem (d.mem_range_self q)).trans
      ((dist_pi_le_iff (by linarith : 0 ≤ C + η)).mpr fun e => by
        simpa [dist_eq_norm, a, d] using hq e.val.1 e.val.2 e.property)
  refine ⟨p, fun u v huv => ?_⟩
  have hh := (dist_pi_le_iff hC).mp hd (⟨(u, v), huv⟩ : I)
  simpa [dist_eq_norm, a, d] using hh

end SimpleGraph
