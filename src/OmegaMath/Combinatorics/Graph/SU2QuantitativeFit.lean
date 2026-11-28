import OmegaMath.Geometry.SU2ErrorTransfer
import OmegaMath.Geometry.SU2ExpRemainder
import OmegaMath.Geometry.SU2EuclideanCoordinates
import OmegaMath.Combinatorics.Graph.SU2TangentTransfer

/-! Omega original.

Quantitative transfer of fixed-graph fitting witnesses. The reverse direction
allows every unit-quaternion potential and uses normalized ambient differences.
-/

noncomputable section
open scoped Quaternion InnerProductSpace

namespace SimpleGraph.SU2Tangent

open Omega.Geometry.UnitQuaternion

variable {V : Type*} {G : SimpleGraph V}

/-- Every arbitrary round potential with error at most `t * C` supplies an
additive potential with this explicit error. No logarithms or smallness
assumptions are required. -/
theorem additive_fit_of_round_fit (o : V) {D M C t : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hC : 0 ≤ C) (ht : 0 < t)
    (hpath : ∀ v, ∃ w : G.Walk o v, (w.length : ℝ) ≤ D)
    (a : V → V → R3)
    (ha : ∀ u v, G.Adj u v → ‖a u v‖ ≤ M)
    (p : V → U)
    (hp : ∀ u v, G.Adj u v →
      roundDist (expPath (toQuat (a u v)) (toQuat_re _) t) ((p u)⁻¹ * p v) ≤ t * C) :
    ∃ q : V → R3, ∀ u v, G.Adj u v →
      ‖a u v - (q v - q u)‖ ≤ C + t * (M ^ 2 / 2 + D * (M + C) * M) := by
  let g (u v : V) := expPath (toQuat (a u v)) (toQuat_re _) t
  let P (v : V) : U := (p o)⁻¹ * p v
  have hP : ∀ u v, G.Adj u v → roundDist (g u v) ((P u)⁻¹ * P v) ≤ t * C := by
    intro u v huv
    convert hp u v huv using 1
    dsimp [P, g]
    group
  have hg (u v : V) (huv : G.Adj u v) : ‖(g u v : ℍ[ℝ]) - 1‖ ≤ t * M := by
    exact (exp_chord_le (toQuat (a u v)) (toQuat_re _) ht.le).trans
      (by rw [toQuat_norm]; exact mul_le_mul_of_nonneg_left (ha u v huv) ht.le)
  have hpedge : ∀ u v, G.Adj u v → ‖(P u : ℍ[ℝ]) * g u v - P v‖ ≤ t * C := by
    intro u v huv
    exact (chord_le_round (P u * g u v) (P v)).trans
      (by simpa only [← round_edge] using hP u v huv)
  have hstep : ∀ u v, G.Adj u v → ‖(P v : ℍ[ℝ]) - P u‖ ≤ t * (M + C) := by
    intro u v huv
    have he : (P v : ℍ[ℝ]) - P u =
        ((P v : ℍ[ℝ]) - (P u : ℍ[ℝ]) * g u v) +
        (P u : ℍ[ℝ]) * ((g u v : ℍ[ℝ]) - 1) := by noncomm_ring
    rw [he]
    have h₁ := hpedge u v huv
    rw [norm_sub_rev] at h₁
    have h₂ : ‖(P u : ℍ[ℝ]) * ((g u v : ℍ[ℝ]) - 1)‖ ≤ t * M := by
      simpa only [norm_mul, norm_coe, one_mul] using hg u v huv
    exact (norm_add_le _ _).trans (by linarith)
  have hroot (v : V) : ‖(P v : ℍ[ℝ]) - 1‖ ≤ t * D * (M + C) := by
    obtain ⟨w, hw⟩ := hpath v
    have h := walk_bound w (fun v => (P v : ℍ[ℝ])) hstep
    have ho : (P o : ℍ[ℝ]) = 1 := by simp [P]
    rw [ho] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hw (show 0 ≤ t * (M + C) by positivity)])
  let Q (v : V) := t⁻¹ • ((P v : ℍ[ℝ]) - 1)
  refine ⟨fun v => fromQuat (Q v), fun u v huv => ?_⟩
  have hs : ‖toQuat (a u v) - t⁻¹ • ((g u v : ℍ[ℝ]) - 1)‖ ≤ t * M ^ 2 / 2 := by
    exact (exp_slope_error_le (toQuat (a u v)) (toQuat_re _) ht).trans
      (by rw [toQuat_norm]; nlinarith [(sq_le_sq₀ (norm_nonneg (a u v)) hM).mpr (ha u v huv)])
  have h := ambient_residual_bound (toQuat (a u v)) (P u) (P v) (g u v)
    ht hM (by positivity : 0 ≤ t * D * (M + C)) hs (hg u v huv)
    (hroot u) (hpedge u v huv)
  have he : a u v - (fromQuat (Q v) - fromQuat (Q u)) =
      fromQuat (toQuat (a u v) - (Q v - Q u)) := by simp
  rw [he]
  exact (fromQuat_norm_le _).trans (h.trans_eq (by ring))

/-- Exponentiating any additive fitting witness of error at most `R ≤ M`
gives the source's explicit upper error, after a root gauge. -/
theorem round_fit_of_additive_fit (o : V) {D M R t : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (ht : 0 ≤ t) (hR : R ≤ M)
    (hpath : ∀ v, ∃ w : G.Walk o v, (w.length : ℝ) ≤ D)
    (a : V → V → R3)
    (ha : ∀ u v, G.Adj u v → ‖a u v‖ ≤ M)
    (q : V → R3) (hq : ∀ u v, G.Adj u v → ‖a u v - (q v - q u)‖ ≤ R)
    (hsmall : t * (M * (1 + 4 * D)) ≤ Real.pi) :
    ∃ p : V → U, ∀ u v, G.Adj u v →
      roundDist (expPath (toQuat (a u v)) (toQuat_re _) t) ((p u)⁻¹ * p v) ≤
        t * R + 4 * D * (D + 1) * M ^ 2 * t ^ 2 := by
  let Q (v : V) := toQuat (q v - q o)
  have hstep : ∀ u v, G.Adj u v → ‖q v - q u‖ ≤ 2 * M := by
    intro u v huv
    have he : q v - q u = a u v - (a u v - (q v - q u)) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [ha u v huv, hq u v huv])
  have hroot (v : V) : ‖Q v‖ ≤ 2 * D * M := by
    obtain ⟨w, hw⟩ := hpath v
    have h := walk_bound w (fun v => toQuat (q v)) (fun u v huv => by
      simpa only [← map_sub, toQuat_norm] using hstep u v huv)
    rw [← map_sub, toQuat_norm] at h
    dsimp [Q]
    rw [toQuat_norm]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hw (by positivity : 0 ≤ 2 * M)])
  refine ⟨fun v => expPath (Q v) (toQuat_re _) t, fun u v huv => ?_⟩
  have h := edge_error_le (toQuat (a u v)) (Q u) (Q v) (toQuat_re _)
    (toQuat_re _) (toQuat_re _) ht hM hD (by simpa only [toQuat_norm] using ha u v huv)
    (hroot u) (hroot v) hsmall
  have he : toQuat (a u v) - (Q v - Q u) = toQuat (a u v - (q v - q u)) := by
    simp only [Q, map_sub]
    abel
  rw [he, toQuat_norm] at h
  have h' := (abs_le.mp h).2
  nlinarith [mul_le_mul_of_nonneg_left (hq u v huv) ht]

end SimpleGraph.SU2Tangent
