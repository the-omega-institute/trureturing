/- GID: D5/S3/Geometry/NonlinearSkewRigidity
   generality: G
   mirror-B: D5/B/S3/Geometry/NonlinearSkewRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.LinearMap]
   utility: none
   digest: A local acute patch forces rigidity of an initially arbitrary inner-product map. -/

module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Tactic

/-! Rigidity from a product identity on an arbitrary real inner product space. -/

@[expose] public section
noncomputable section

open Set Metric Topology Filter
open scoped InnerProductSpace

namespace D5.S3.Geometry.NonlinearSkewRigidity

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem inner_open_separates {U : Set W} (hU : IsOpen U) (hne : U.Nonempty)
    {q : W} (h : ∀ b ∈ U, ⟪b, q⟫_ℝ = 0) : q = 0 := by
  let L : W →ₗ[ℝ] ℝ := (innerSL ℝ q).toLinearMap
  have hsub : U ⊆ (L.ker : Set W) := by
    intro b hb
    change ⟪q, b⟫_ℝ = 0
    rw [real_inner_comm]
    exact h b hb
  have ht : L.ker = ⊤ :=
    L.ker.eq_top_of_nonempty_interior' (hne.mono (interior_maximal hsub hU))
  have hq : q ∈ L.ker := by rw [ht]; trivial
  exact inner_self_eq_zero.mp hq

private theorem inner_open_ext {U : Set W} (hU : IsOpen U) (hne : U.Nonempty)
    {p q : W} (h : ∀ b ∈ U, ⟪b, p⟫_ℝ = ⟪b, q⟫_ℝ) : p = q := by
  apply sub_eq_zero.mp
  apply inner_open_separates hU hne
  intro b hb
  rw [inner_sub_right, h b hb, sub_self]

private theorem small_scale (w : W) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ‖t • w‖ < ε := by
  let t := ε / (‖w‖ + 1)
  have hd : 0 < ‖w‖ + 1 := by positivity
  have ht : 0 < t := div_pos hε hd
  have he : t * (‖w‖ + 1) = ε := div_mul_cancel₀ _ hd.ne'
  refine ⟨t, ht, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  nlinarith

private theorem acute_ball {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {v : W} (hv : v ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ ball v (3 * ε), ∀ c ∈ ball v (3 * ε),
      r ^ 2 * ‖b‖ * ‖c‖ < ⟪b, c⟫_ℝ := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hp : 0 < ⟪v, v⟫_ℝ - r ^ 2 * ‖v‖ * ‖v‖ := by
    rw [real_inner_self_eq_norm_sq]
    have hr2 : r ^ 2 < 1 := by nlinarith
    have := mul_pos (sub_pos.mpr hr2) (sq_pos_of_pos hvp)
    nlinarith only [this]
  have hc : Continuous (fun p : W × W =>
      ⟪p.1, p.2⟫_ℝ - r ^ 2 * ‖p.1‖ * ‖p.2‖) := by fun_prop
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((hc.tendsto (v, v)).eventually (Ioi_mem_nhds hp))
  refine ⟨δ / 3, by positivity, ?_⟩
  intro b hb c hcc
  have hh : (b, c) ∈ ball (v, v) δ := by
    rw [← ball_prod_same]
    constructor
    · convert hb using 1 <;> ring
    · convert hcc using 1 <;> ring
  have := hball hh
  dsimp at this
  linarith

private theorem skew_of_acute {r : ℝ} (F : W → W)
    (hnorm : ∀ y, ‖F y‖ = r * ‖y‖)
    (hprod : ∀ y z, (⟪y, z⟫_ℝ + ⟪F y, F z⟫_ℝ) *
      (⟪y, F z⟫_ℝ + ⟪F y, z⟫_ℝ) = 0)
    {b c : W} (hacute : r ^ 2 * ‖b‖ * ‖c‖ < ⟪b, c⟫_ℝ) :
    ⟪b, F c⟫_ℝ = -⟪F b, c⟫_ℝ := by
  have hbound := neg_le_abs (⟪F b, F c⟫_ℝ)
  have hcs := abs_real_inner_le_norm (F b) (F c)
  rw [hnorm, hnorm] at hcs
  have hfirst : 0 < ⟪b, c⟫_ℝ + ⟪F b, F c⟫_ℝ := by nlinarith
  have hsecond := (mul_eq_zero.mp (hprod b c)).resolve_left hfirst.ne'
  linarith

/-- A strict acute neighborhood gives an exact difference identity on the original carrier. -/
theorem exists_acute_skew_difference {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (F : W → W) (hnorm : ∀ y, ‖F y‖ = r * ‖y‖)
    (hprod : ∀ y z, (⟪y, z⟫_ℝ + ⟪F y, F z⟫_ℝ) *
      (⟪y, F z⟫_ℝ + ⟪F y, z⟫_ℝ) = 0)
    {v : W} (hv : v ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ b ∈ ball v (3 * ε), ∀ c ∈ ball v (3 * ε),
        r ^ 2 * ‖b‖ * ‖c‖ < ⟪b, c⟫_ℝ) ∧
      (∀ b ∈ ball v (3 * ε), ∀ c ∈ ball v (3 * ε),
        ⟪b, F c⟫_ℝ = -⟪F b, c⟫_ℝ) ∧
      (∀ h, ‖h‖ < ε → ∀ b ∈ ball v ε,
        ⟪b, F (v + h) - F v⟫_ℝ = -⟪F b, h⟫_ℝ) := by
  obtain ⟨ε, hε, ha⟩ := acute_ball hr hr1 hv
  have hs := fun b hb c hc => skew_of_acute F hnorm hprod (ha b hb c hc)
  refine ⟨ε, hε, ha, hs, ?_⟩
  intro h hh b hb
  have hb' : b ∈ ball v (3 * ε) := ball_subset_ball (by linarith) hb
  have hv' : v ∈ ball v (3 * ε) := mem_ball_self (by linarith)
  have hsum : v + h ∈ ball v (3 * ε) := by
    rw [mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hh.trans (by linarith : ε < 3 * ε)
  have h1 := hs b hb' (v + h) hsum
  have h2 := hs b hb' v hv'
  simp only [inner_sub_right, inner_add_right] at h1 h2 ⊢
  linarith

end D5.S3.Geometry.NonlinearSkewRigidity
