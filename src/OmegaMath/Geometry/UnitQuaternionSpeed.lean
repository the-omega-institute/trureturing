import OmegaMath.Geometry.SU2TangentGeometry
import Mathlib.Analysis.Calculus.MeanValue

/-! Omega original.

Sharp conversion of ambient quaternion speed into round distance. The proof uses
the first-order chord/round comparison and the real one-sided fencing theorem.
-/

noncomputable section
open scoped Quaternion InnerProductSpace Topology
open Filter Set

namespace Omega.Geometry.UnitQuaternion

local notation "U" => unitary ℍ[ℝ]

/-- Distance from a fixed point is continuous along an ambient continuous curve. -/
theorem continuous_round_of_ambient {p : ℝ → U}
    (hp : Continuous (fun t => (p t : ℍ[ℝ]))) (q : U) :
    Continuous (fun t => roundDist q (p t)) := by
  exact Real.continuous_arccos.comp (continuous_const.inner hp)

/-- The infinitesimal round speed equals ambient speed at every parameter. -/
theorem round_speed {p : ℝ → U} {v : ℍ[ℝ]} {x : ℝ}
    (hp : HasDerivAt (fun t => (p t : ℍ[ℝ])) v x) :
    Tendsto (fun z => roundDist (p x) (p z) / (z - x)) (𝓝[>] x) (𝓝 ‖v‖) := by
  have hshift : HasDerivAt (fun t => (p (t + x) : ℍ[ℝ])) v 0 := by
    convert hp.scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).add_const x) (by simp) using 1 <;>
      simp [Function.comp_def]
  have h := SimpleGraph.SU2Tangent.round_slope
    (hasDerivAt_const (0 : ℝ) (p x : ℍ[ℝ])) hshift (by simp)
  simp only [zero_sub, norm_neg] at h
  have hsub : Tendsto (fun z : ℝ => z - x) (𝓝[>] x) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((continuousAt_id (x := x)).sub_const x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr (show x < z from hz)
  convert h.comp hsub using 1
  ext z
  simp

/-- A differentiable scalar barrier whose derivative bounds ambient speed also
bounds round displacement. This retains the sharp constant one. -/
theorem round_le_of_speed_le {p : ℝ → U} {v : ℝ → ℍ[ℝ]} {a b : ℝ}
    (hp : ∀ t, HasDerivAt (fun s => (p s : ℍ[ℝ])) (v t) t)
    {B B' : ℝ → ℝ} (hB : ∀ t, HasDerivAt B (B' t) t)
    (hzero : B a = 0)
    (hbound : ∀ t ∈ Ico a b, ‖v t‖ ≤ B' t) (hab : a ≤ b) :
    roundDist (p a) (p b) ≤ B b := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun t => roundDist (p a) (p t))
    ((continuous_round_of_ambient (continuous_iff_continuousAt.mpr
      (fun t => (hp t).continuousAt)) (p a)).continuousOn)
    (by simp [hzero])
    (continuous_iff_continuousAt.mpr (fun t => (hB t).continuousAt)).continuousOn
    (fun t _ => (hB t).hasDerivWithinAt) ?_ ⟨hab, le_rfl⟩
  intro t ht r hr
  have he := (round_speed (hp t)).eventually
    (gt_mem_nhds (lt_of_le_of_lt (hbound t ht) hr))
  apply Filter.Eventually.frequently
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzt
  have htri := round_triangle (p a) (p t) (p z)
  rw [slope_def_field]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hzt).le) hz

end Omega.Geometry.UnitQuaternion
