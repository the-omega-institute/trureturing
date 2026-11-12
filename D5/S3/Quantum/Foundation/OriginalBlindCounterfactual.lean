/- GID: D5/S3/Quantum/Foundation/OriginalBlindCounterfactual
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalBlindCounterfactual
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Module.HahnBanach]
   utility: none
   digest: Original signed blind directions yield distinct states and a full proper separator. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Tactic.Module

/-! Symmetric counterfactuals on the entire normalized base of the original cone. -/

noncomputable section
open Set Filter
open scoped Topology Pointwise

namespace D5.S3.Quantum.Foundation.OriginalBlindCounterfactual

open CircuitBalancedConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem normalized_interior [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ w ∈ base C u, w ∈ interior (C : Set V) := by
  let : PerfectSpace V := perfectSpace_of_module ℝ V
  have hint : (interior (C : Set V)).Nonempty := by
    apply C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ C.zero_mem), hgen]
    rfl
  obtain ⟨c, hc, hcne⟩ :=
    (dense_compl_singleton (0 : V)).inter_open_nonempty _ isOpen_interior hint
  have hc0 : c ≠ 0 := by simpa using hcne
  have huc : 0 < u c := hstrict c (interior_subset hc) hc0
  have hscale : (u c)⁻¹ • (C : Set V) = (C : Set V) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact C.smul_mem (inv_pos.mpr huc).le hy
    · intro hx
      refine ⟨u c • x, C.smul_mem huc.le hx, ?_⟩
      simp [smul_smul, huc.ne']
  refine ⟨(u c)⁻¹ • c, normalized_mem hstrict (interior_subset hc) hc0, ?_⟩
  rw [← hscale, interior_smul₀ (inv_ne_zero huc.ne')]
  exact smul_mem_smul_set hc

private theorem proper_detects_direction
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {z : V} (hz : z ≠ 0) (huz : u z = 0) :
    ∃ f : V →ₗ[ℝ] ℝ, proper C u f ∧ 0 < f z := by
  have hK := base_compact hclosed hstrict
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨l, hl, hlz⟩ := exists_dual_vector ℝ z (norm_ne_zero_iff.mpr hz)
  let f : V →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • u + (1 / (2 * R)) • l.toLinearMap
  have hf : proper C u f := by
    apply cone_bound hK hstrict
    intro p
    have habs : |l p| ≤ R := by
      have hh := l.le_opNorm (p : V)
      simpa [hl] using hh.trans (by simpa [hl] using hbound p (pure_mem p))
    have hsmall : |(1 / (2 * R)) * l p| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * R))]
      apply (mul_le_mul_of_nonneg_left habs (by positivity)).trans_eq
      field_simp
    have hfp : f p = 1 / 2 + (1 / (2 * R)) * l p := by
      simp [f, (pure_mem p).2]
    rw [hfp]
    constructor <;> linarith [(abs_le.mp hsmall).1, (abs_le.mp hsmall).2]
  refine ⟨f, hf, ?_⟩
  have hfz : f z = (1 / (2 * R)) * ‖z‖ := by simp [f, huz, hlz]
  rw [hfz]
  exact mul_pos (by positivity) (norm_pos_iff.mpr hz)

/-- A signed vector invisible to a linear readout gives two distinct actual original
states with that same readout, while one full original proper effect distinguishes them.
The center and both states lie in the original cone interior. -/
theorem original_blind_direction_counterfactual
    {O : Type*} [AddCommGroup O] [Module ℝ O]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (T : V →ₗ[ℝ] O) {z : V} (hz : z ≠ 0) (huz : u z = 0) (hTz : T z = 0) :
    ∃ (w : V) (e : ℝ) (f : V →ₗ[ℝ] ℝ),
      w ∈ base C u ∧ w ∈ interior (C : Set V) ∧ 0 < e ∧ proper C u f ∧
      w + e • z ∈ base C u ∧ w - e • z ∈ base C u ∧
      w + e • z ∈ interior (C : Set V) ∧ w - e • z ∈ interior (C : Set V) ∧
      w + e • z ≠ w - e • z ∧ T (w + e • z) = T (w - e • z) ∧
      0 < f (w + e • z) - f (w - e • z) := by
  let : Nontrivial V := nontrivial_of_ne z 0 hz
  obtain ⟨w, hwK, hwint⟩ := normalized_interior hstrict hgen
  have hplus : ∀ᶠ t : ℝ in 𝓝 0, w + t • z ∈ interior (C : Set V) := by
    apply (show Continuous (fun t : ℝ => w + t • z) from
      continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 w
        (by simp) |>.eventually_mem
    exact isOpen_interior.mem_nhds hwint
  have hminus : ∀ᶠ t : ℝ in 𝓝 0, w - t • z ∈ interior (C : Set V) := by
    apply (show Continuous (fun t : ℝ => w - t • z) from
      continuous_const.sub (continuous_id.smul continuous_const)).tendsto' 0 w
        (by simp) |>.eventually_mem
    exact isOpen_interior.mem_nhds hwint
  obtain ⟨e, he, heplus, heminus⟩ := (hplus.and hminus).exists_gt
  obtain ⟨f, hf, hfz⟩ := proper_detects_direction hclosed hstrict hz huz
  refine ⟨w, e, f, hwK, hwint, he, hf, ?_, ?_, heplus, heminus, ?_, ?_, ?_⟩
  · exact ⟨interior_subset heplus, by simp [map_add, map_smul, hwK.2, huz]⟩
  · exact ⟨interior_subset heminus, by simp [map_sub, map_smul, hwK.2, huz]⟩
  · intro h
    have hh : (2 * e) • z = 0 := by
      calc
        (2 * e) • z = (w + e • z) - (w - e • z) := by module
        _ = 0 := sub_eq_zero.mpr h
    exact hz ((smul_eq_zero.mp hh).resolve_left (by positivity))
  · simp [map_add, map_sub, map_smul, hTz]
  · simp only [map_add, map_sub, map_smul, smul_eq_mul]
    nlinarith

end D5.S3.Quantum.Foundation.OriginalBlindCounterfactual
