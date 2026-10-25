import CFMPGenericEveryEdge1522Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceCapEdge1526Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate
open D5.S3.Geometry.Gluing.RawFaceEveryEdge1522Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate (PointQuotient)
open Topology Set
variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

theorem every_actual_cap_edge_chart (P : RawFacePairing T) (ν : Vertex P)
    (x : Point P ν) (f : Fin 4) (hx : EdgePoint P x f) :
    ∃ V : Set ↥(quotientSlice P ν), IsOpen V ∧
      actualSliceQuotientHomeomorph P ν
        ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) x) ∈ V ∧
      ∃ a b δ : ℝ, 0 < δ ∧ Nonempty (↥V ≃ₜ ↥(rectangle a b δ)) := by
  obtain ⟨U,hU,hxU,a,b,δ,hδ,⟨e⟩⟩ := every_original_edge_chart P ν x f hx
  let h := actualSliceQuotientHomeomorph P ν
  refine ⟨h '' U,h.isOpenMap U hU,?_,a,b,δ,hδ,?_⟩
  · exact ⟨_,hxU,rfl⟩
  · exact ⟨(h.image U).symm.trans e⟩

end D5.S3.Geometry.Gluing.RawFaceCapEdge1526Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCapEdge1526Candidate.every_actual_cap_edge_chart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1526 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1526 disallowed {ax}"
    Lean.logInfo m!"CFMP1526 CHECKED {name} axioms={axioms}"
