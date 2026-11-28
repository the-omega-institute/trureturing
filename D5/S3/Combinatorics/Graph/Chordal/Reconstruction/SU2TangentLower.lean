/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euclidean-three transfer and width-four round SU2 family lower bound. -/

import OmegaMath.Combinatorics.Graph.SU2TangentTransfer
import OmegaMath.Geometry.SU2EuclideanCoordinates
import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! Euclidean-three transfer and width-four round SU2 family lower bound. -/

noncomputable section
open scoped Quaternion InnerProductSpace BigOperators
namespace SimpleGraph.SU2Tangent

open Omega.Geometry.UnitQuaternion

/-- The fixed-graph coefficient comparison. The graph is held fixed while the
quaternion gains shrink, and potentials in both targets are unrestricted. -/
theorem fixed_graph_euclidean_three_transfer {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) {C : ℝ} (hC : 0 ≤ C)
    (hupper : RoundUpper G C) : PairRetention.Upper G R3 C := by
  intro a hrev htri
  obtain ⟨p, hp⟩ := fixed_graph_pure_transfer hG hC hupper
    (fun u v => toQuat (a u v)) (fun _ _ => rfl)
    (fun u v => by rw [hrev, map_neg]) (fun u v w huv hvw huw => by
      rw [← map_add, ← map_sub, toQuat_norm]
      exact htri u v w huv hvw huw)
  refine ⟨fun v => fromQuat (p v), fun u v huv => ?_⟩
  have hh := (fromQuat_norm_le (toQuat (a u v) - (p v - p u))).trans (hp u v huv)
  simpa only [map_sub, from_to, PairRetention.residual] using hh

/-- The coefficient comparison at every nonnegative defect scale, including
zero. The closure lemma removes the positive normalization slack. -/
theorem fixed_graph_euclidean_three_scaled {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) {C : ℝ} (hC : 0 ≤ C)
    (hupper : RoundUpper G C) (a : V → V → R3) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ u v, a v u = -a u v)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w →
      ‖a u v + a v w - a u w‖ ≤ δ) :
    ∃ p : V → R3, ∀ u v, G.Adj u v → ‖a u v - (p v - p u)‖ ≤ C * δ := by
  apply exists_gain_fit_of_forall_pos G a (mul_nonneg hC hδ)
  intro η hη
  let d := δ + η / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hδd : δ ≤ d := le_add_of_nonneg_right (div_nonneg hη.le hden.le)
  obtain ⟨p, hp⟩ := fixed_graph_euclidean_three_transfer hG hC hupper
    (fun u v => d⁻¹ • a u v) (fun u v => by rw [hrev, smul_neg])
    (fun u v w huv hvw huw => by
      change ‖d⁻¹ • a u v + d⁻¹ • a v w - d⁻¹ • a u w‖ ≤ 1
      rw [← smul_add, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
      exact (mul_le_mul_of_nonneg_left ((htri u v w huv hvw huw).trans hδd)
        (inv_nonneg.mpr hd.le)).trans_eq (inv_mul_cancel₀ hd.ne'))
  refine ⟨fun v => d • p v, fun u v huv => ?_⟩
  have he : a u v - (d • p v - d • p u) =
      d • (d⁻¹ • a u v - (p v - p u)) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hd.ne', one_smul, smul_sub]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
  have hh := mul_le_mul_of_nonneg_left (hp u v huv) hd.le
  have hslack : C * (η / (C + 1)) ≤ η := by
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  exact hh.trans (by dsimp [d]; nlinarith)

/-- A regular diameter-one tetrahedron in Euclidean three-space. -/
private def tetrahedron (i : Fin 4) : R3 :=
  let r := Real.sqrt 2 / 4
  ![WithLp.toLp 2 ![r,r,r], WithLp.toLp 2 ![r,-r,-r],
    WithLp.toLp 2 ![-r,r,-r], WithLp.toLp 2 ![-r,-r,r]] i

private theorem tetrahedron_sum : ∑ i, tetrahedron i = 0 := by
  ext j
  fin_cases j <;> simp [tetrahedron, Fin.sum_univ_four]

private theorem tetrahedron_diameter (a b : Fin 4) : ‖tetrahedron a - tetrahedron b‖ ≤ 1 := by
  have hh := EuclideanSpace.real_norm_sq_eq (tetrahedron a - tetrahedron b)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnon := norm_nonneg (tetrahedron a - tetrahedron b)
  fin_cases a <;> fin_cases b <;>
    simp [tetrahedron, Fin.sum_univ_three] at hh hnon ⊢ <;> nlinarith

private theorem tetrahedron_doubled_norm (a : Fin 4) :
    ‖(2 : ℝ) • tetrahedron a‖ ^ 2 = (Real.sqrt (3 / 2 : ℝ)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Real.sq_sqrt (by norm_num)]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  fin_cases a <;> simp [tetrahedron, Fin.sum_univ_three] <;> nlinarith

/-- This is the same centred affine sum obstruction used by
`hilbert_powerPath_uniform_lower`, instantiated in dimension three. -/
private theorem tetrahedron_radius (y : R3) :
    ∃ a : Fin 4, Real.sqrt (3 / 2 : ℝ) ≤ ‖(2 : ℝ) • tetrahedron a - y‖ := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ
    (fun i => ‖(2 : ℝ) • tetrahedron i - y‖) Finset.univ_nonempty
  refine ⟨a, FiniteHilbertJung.radius_lower_of_centred_constant_norm
    (fun i => (2 : ℝ) • tetrahedron i) (Real.sqrt (3 / 2 : ℝ)) _ y ?_
    tetrahedron_doubled_norm (fun i => ha i (Finset.mem_univ i))⟩
  rw [← Finset.smul_sum, tetrahedron_sum, smul_zero]

private theorem pathPower_connected {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (BanachPathPower.pathPower n k).Connected := by
  apply (connected_pathGraph.mpr (by omega : n ≠ 0)).mono
  intro a b hab
  rcases pathGraph_adj.mp hab with h | h
  · exact ⟨by intro he; have := congrArg Fin.val he; omega, by omega, by omega⟩
  · exact ⟨by intro he; have := congrArg Fin.val he; omega, by omega, by omega⟩

/-- The width-four lower bound is a family supremum: one coefficient that
works on every finite width-four path is at least sqrt(3/2). It asserts no
such lower bound for every individual finite graph. -/
theorem round_width_four_family_lower {C : ℝ} (hC : 0 ≤ C)
    (hfit : ∀ n, RoundUpper (BanachPathPower.pathPower n 4) C) :
    Real.sqrt (3 / 2 : ℝ) ≤ C := by
  apply BanachPathPower.powerPath_uniform_ge_doubled_radius (by decide : 0 < 4) hC
    (x := tetrahedron) (hd := tetrahedron_diameter) (hr := tetrahedron_radius)
  intro n
  by_cases hn : 0 < n
  · exact fixed_graph_euclidean_three_transfer (pathPower_connected hn (by decide)) hC (hfit n)
  · have hn0 : n = 0 := by omega
    subst n
    intro a _ _
    exact ⟨fun v => Fin.elim0 v, fun u => Fin.elim0 u⟩

/-- Each subcritical proposed coefficient fails on an actual finite width-four
path, with fully ambient SU(2) potentials and a positive triangle bound. -/
private theorem round_width_four_finite_obstruction {C : ℝ} (hC : 0 ≤ C)
    (hlt : C < Real.sqrt (3 / 2 : ℝ)) :
    ∃ n, ¬ RoundUpper (BanachPathPower.pathPower n 4) C := by
  by_contra! h
  exact (not_lt_of_ge (round_width_four_family_lower hC h)) hlt

/-- An expanded finite counterexample statement, displaying the gain, defect
bound, and the universal quantifier over ambient quaternion potentials. -/
theorem exists_round_width_four_obstruction {C : ℝ} (hC : 0 ≤ C)
    (hlt : C < Real.sqrt (3 / 2 : ℝ)) :
    ∃ (n : ℕ) (g : Fin n → Fin n → U) (δ : ℝ), 0 < δ ∧
      (∀ u v, (BanachPathPower.pathPower n 4).Adj u v → g v u = (g u v)⁻¹) ∧
      (∀ u v w, (BanachPathPower.pathPower n 4).Adj u v →
        (BanachPathPower.pathPower n 4).Adj v w →
        (BanachPathPower.pathPower n 4).Adj u w → roundDist (g u v * g v w) (g u w) ≤ δ) ∧
      ∀ p : Fin n → U, ∃ u v, (BanachPathPower.pathPower n 4).Adj u v ∧
        C * δ < roundDist (g u v) ((p u)⁻¹ * p v) := by
  obtain ⟨n, hn⟩ := round_width_four_finite_obstruction hC hlt
  unfold RoundUpper at hn
  push Not at hn
  exact ⟨n, hn⟩

end SimpleGraph.SU2Tangent
