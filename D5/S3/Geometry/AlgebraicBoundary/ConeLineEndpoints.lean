/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeLineEndpoints
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeLineEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Off-axis lines cut closed salient cones and their negatives in separated closed rays. -/

import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic

/-! Actual boundary endpoints of lines in arbitrary interior cone directions. -/

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_line_mem (C : ConvexCone ℝ E) {e : E}
    (he : e ∈ interior (C : Set E)) (x : E) :
    ∃ t : ℝ, 0 < t ∧ t • e - x ∈ C := by
  have htend : Tendsto (fun t : ℝ => e - t⁻¹ • x) atTop (𝓝 e) := by
    simpa using tendsto_const_nhds.sub
      ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul_const x)
  have hmem := htend.eventually (mem_interior_iff_mem_nhds.mp he)
  obtain ⟨t, ht, htx⟩ := ((eventually_gt_atTop (0 : ℝ)).and hmem).exists
  refine ⟨t, ht, ?_⟩
  have h := C.smul_mem ht htx
  simpa only [smul_sub, smul_smul, mul_inv_cancel₀ ht.ne', one_smul] using h

private theorem right_endpoint (C : ConvexCone ℝ E) (hclosed : IsClosed (C : Set E))
    (hs : C.Salient) {e x : E} (he : e ∈ interior (C : Set E))
    (hx : ∀ s : ℝ, x ≠ s • e) :
    ∃ b : ℝ, {t : ℝ | t • e - x ∈ C} = Ici b ∧
      b • e - x ∈ frontier (C : Set E) := by
  let S : Set ℝ := {t : ℝ | t • e - x ∈ C}
  have hup : IsUpperSet S := by
    intro t u htu ht
    rcases eq_or_lt_of_le htu with rfl | htu
    · exact ht
    · have h := C.add_mem ht (C.smul_mem (sub_pos.mpr htu) (interior_subset he))
      have heq : t • e - x + (u - t) • e = u • e - x := by
        rw [sub_smul]
        abel
      change u • e - x ∈ C
      rwa [heq] at h
  have hdis : ∀ t : ℝ, ¬ (t • e - x ∈ C ∧ -(t • e - x) ∈ C) := by
    intro t h
    exact hs _ h.1 (fun hz => hx t (sub_eq_zero.mp hz).symm) h.2
  obtain ⟨u, _, hu⟩ := exists_line_mem C he (-x)
  have hneg : -((-u) • e - x) ∈ C := by simpa [add_comm] using hu
  have hbelow : BddBelow S := by
    refine ⟨-u, fun t ht => le_of_not_gt (fun h => ?_)⟩
    exact hdis (-u) ⟨hup h.le ht, hneg⟩
  have hnonempty : S.Nonempty := by
    obtain ⟨t, _, ht⟩ := exists_line_mem C he x
    exact ⟨t, ht⟩
  have hSclosed : IsClosed S :=
    hclosed.preimage ((continuous_id.smul continuous_const).sub continuous_const)
  have hSeq : S = Ici (sInf S) := by
    rw [← upperClosure_eq_Ici_csInf hnonempty hbelow hSclosed]
    exact (upperClosure_eq.mpr hup).symm
  refine ⟨sInf S, hSeq, ?_⟩
  have hfront : sInf S ∈ frontier S := by rw [hSeq, frontier_Ici]; simp
  exact ((continuous_id.smul continuous_const).sub continuous_const).frontier_preimage_subset
    (C : Set E) hfront

/-- For every interior cone direction and every off-axis translate, the actual
cone and its negative cut the line into two strictly separated closed rays.
Both finite endpoints belong to the entire topological cone boundary. -/
theorem off_axis_closed_rays (C : ConvexCone ℝ E) (hclosed : IsClosed (C : Set E))
    (hs : C.Salient) {e x : E} (he : e ∈ interior (C : Set E))
    (hx : ∀ s : ℝ, x ≠ s • e) :
    ∃ a b : ℝ, a < b ∧
      {t : ℝ | -(t • e - x) ∈ C} = Iic a ∧
      {t : ℝ | t • e - x ∈ C} = Ici b ∧
      -(a • e - x) ∈ frontier (C : Set E) ∧
      b • e - x ∈ frontier (C : Set E) := by
  obtain ⟨b, hb, hbf⟩ := right_endpoint C hclosed hs he hx
  have hnx : ∀ s : ℝ, -x ≠ s • e := by
    intro s h
    apply hx (-s)
    simpa using congrArg Neg.neg h
  obtain ⟨c, hc, hcf⟩ := right_endpoint C hclosed hs he hnx
  have hneg : {t : ℝ | -(t • e - x) ∈ C} = Iic (-c) := by
    ext t
    have ht : -(t • e - x) = (-t) • e - (-x) := by
      simp [sub_eq_add_neg, add_comm]
    change (-(t • e - x) ∈ C) ↔ t ≤ -c
    rw [ht]
    change (-t ∈ {s : ℝ | s • e - (-x) ∈ C}) ↔ t ≤ -c
    rw [hc]
    change c ≤ -t ↔ t ≤ -c
    constructor <;> intro h <;> linarith
  have hab : -c < b := by
    by_contra! h
    have hp : (-c) • e - x ∈ C := by
      change -c ∈ {t : ℝ | t • e - x ∈ C}
      rw [hb]
      exact h
    have hn : -((-c) • e - x) ∈ C := by
      change -c ∈ {t : ℝ | -(t • e - x) ∈ C}
      rw [hneg]
      change -c ≤ -c
      exact le_rfl
    exact hs _ hp (fun hz => hx (-c) (sub_eq_zero.mp hz).symm) hn
  refine ⟨-c, b, hab, hneg, hb, ?_, hbf⟩
  simpa [add_comm] using hcf

#print axioms off_axis_closed_rays

end D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints
