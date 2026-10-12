/- GID: D5/S3/Geometry/Hyperideal/ReturnCycleWords
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ReturnCycleWords
   mirror-E: none(waiver:finite-slot-return-cycle)
   anchors: []
   utility: none
   digest: Three face-pairing steps realize the low and high edge return words. -/

import D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

noncomputable section
namespace D5.S3.Geometry.Hyperideal.ReturnCycleWords

open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev edgeClass (u v : G) : Occurrence Ω → Occurrence Ω → Prop :=
  Relation.EqvGen (edgeRel (pairing u v))

/-- The three low-edge slots close with the return word `v⁻¹ * u²`. -/
theorem low_edge_cycle (u v : G) (x : Ω) :
    edgeClass u v (x, 0) (act x v⁻¹, 3) ∧
    edgeClass u v (act x v⁻¹, 3) (act (act x v⁻¹) u, 5) ∧
    edgeClass u v (act (act x v⁻¹) u, 5)
      (act (act (act x v⁻¹) u) u, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((x, 2), 2)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act x v⁻¹, 0), 0)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act (act x v⁻¹) u, 0), 2)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩

/-- The three high-edge slots close with the return word `v² * u`. -/
theorem high_edge_cycle (u v : G) (x : Ω) :
    edgeClass u v (x, 1) (act x v, 2) ∧
    edgeClass u v (act x v, 2) (act (act x v) v, 4) ∧
    edgeClass u v (act (act x v) v, 4)
      (act (act (act x v) v) u, 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((x, 1), 2)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act x v, 1), 1)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act (act x v) v, 0), 1)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩

end D5.S3.Geometry.Hyperideal.ReturnCycleWords
