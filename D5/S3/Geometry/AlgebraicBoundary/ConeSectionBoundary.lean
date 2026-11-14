/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeSectionBoundary
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeSectionBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original positive unit supplies a full compact base and exact entire boundary rays. -/

import D5.S3.Geometry.AlgebraicBoundary.ConeRadialGeometry
import D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation

noncomputable section
open Set
open scoped Topology
namespace D5.S3.Geometry.AlgebraicBoundary.ConeSectionBoundary

open private sectionChart
  from D5.S3.Geometry.AlgebraicBoundary.ConeRadialGeometry
open private base_chart_geometry
  from D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase
open private cone_vertex_frontier cone_frontier_smul
  from D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation
open private cone_interior_add_positive
  from D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

private theorem original_section_boundary {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (hfull : (interior (C : Set E)).Nonempty)
    (u : E →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    let K : Set {x : E | u x = 1} := {x | (x : E) ∈ C}
    IsCompact K ∧ (interior K).Nonempty ∧
      (∃ b : E, u b = 1 ∧ b ∈ interior (C : Set E)) ∧
      (∀ x : {y : E | u y = 1}, x ∈ frontier K ↔ (x : E) ∈ frontier (C : Set E)) ∧
      (∀ x : E, x ∈ frontier (C : Set E) ∧ x ≠ 0 ↔
        ∃ (r : ℝ) (b : {y : E | u y = 1}), 0 < r ∧ b ∈ frontier K ∧ x = r • (b : E)) := by
  dsimp only
  let K : Set {x : E | u x = 1} := {x | (x : E) ∈ C}
  obtain ⟨a, ha⟩ := hfull
  have ha0 : a ≠ 0 := by
    intro h
    have hz := (C.isClosed.frontier_eq ▸ cone_vertex_frontier C hs).2
    exact hz (h ▸ ha)
  have hua := hu a (interior_subset ha) ha0
  let b : E := (u a)⁻¹ • a
  have hb : u b = 1 := by simp [b, map_smul, hua.ne']
  have hbi : b ∈ interior (C : Set E) := by
    simpa [b] using cone_interior_add_positive C ha C.toPointedCone.zero_mem (inv_pos.mpr hua)
  let e := sectionChart u b hb
  let A : Set u.ker := {v | b + (v : E) ∈ C}
  have hpre : e ⁻¹' K = A := rfl
  have hgeo := base_chart_geometry C u b hb
  have hrel : ∀ x : {y : E | u y = 1}, x ∈ frontier K ↔ (x : E) ∈ frontier (C : Set E) := by
    intro x
    obtain ⟨v, rfl⟩ := e.surjective x
    have hefr : e v ∈ frontier K ↔ v ∈ frontier A := by
      change v ∈ e ⁻¹' frontier K ↔ v ∈ frontier A
      rw [e.preimage_frontier K, hpre]
    exact hefr.trans (hgeo.2 v)
  have hcompact : IsCompact K := by
    have he := (isClosed_eq u.continuous
      (continuous_const : Continuous (fun _ : E => (1 : ℝ)))).isClosedEmbedding_subtypeVal
    have hh := he.isCompact_preimage
      (D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.base_compact C.isClosed hu)
    convert hh using 1
    ext x
    change ((x : E) ∈ C) ↔ ((x : E) ∈ C ∧ u (x : E) = 1)
    constructor
    · intro hx
      exact ⟨hx, x.property⟩
    · exact And.left
  refine ⟨hcompact, ?_, ⟨b, hb, hbi⟩, hrel, ?_⟩
  · refine ⟨e 0, ?_⟩
    have hi : (0 : u.ker) ∈ interior A := (hgeo.1 0).mpr (by simpa using hbi)
    change (0 : u.ker) ∈ e ⁻¹' interior K
    rw [e.preimage_interior K, hpre]
    exact hi
  · intro x
    constructor
    · rintro ⟨hx, hx0⟩
      have hux := hu x (C.isClosed.frontier_eq ▸ hx).1 hx0
      let y : {z : E | u z = 1} := ⟨(u x)⁻¹ • x, by simp [map_smul, hux.ne']⟩
      refine ⟨u x, y, hux, (hrel y).mpr (cone_frontier_smul C (inv_pos.mpr hux) hx), ?_⟩
      simp [y, smul_smul, hux.ne']
    · rintro ⟨r, y, hr, hy, rfl⟩
      refine ⟨cone_frontier_smul C hr ((hrel y).mp hy), ?_⟩
      apply smul_ne_zero hr.ne'
      intro hy0
      have hh := y.property
      simpa [hy0] using hh

end D5.S3.Geometry.AlgebraicBoundary.ConeSectionBoundary
