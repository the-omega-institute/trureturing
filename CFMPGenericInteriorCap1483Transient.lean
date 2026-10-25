import CFMPGenericInteriorChart1466Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceInteriorCap1483Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate
open Topology Set
variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

def capInteriorImage (P : RawFacePairing T) (ν : Vertex P) (c : T × Fin 4) :
    Set ↥(quotientSlice P ν) :=
  (actualSliceQuotientHomeomorph P ν) '' quotientInteriorPatch P ν c

theorem cap_interior_image_open (P : RawFacePairing T) (ν : Vertex P) (c : T × Fin 4) :
    IsOpen (capInteriorImage P ν c) :=
  (actualSliceQuotientHomeomorph P ν).isOpen_image.mpr
    (actual_open_interior_quotient P ν c).2

theorem cap_homeomorph_value (P : RawFacePairing T) (ν : Vertex P) (p : Point P ν) :
    ((actualSliceQuotientHomeomorph P ν) (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν))) p)).val =
      (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P)) (toTruncation P p) : TruncatedQuotient P) := by
  rfl

theorem cap_interior_image_representatives (P : RawFacePairing T) (ν : Vertex P)
    (c : T × Fin 4) (z : ↥(quotientSlice P ν)) :
    z ∈ capInteriorImage P ν c ↔
      ∃ p : Point P ν, p ∈ InteriorPatch P ν c ∧
        (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P)) (toTruncation P p) : TruncatedQuotient P) = z.val := by
  constructor
  · rintro ⟨x,⟨p,hp,hpx⟩,hxz⟩
    refine ⟨p,hp,?_⟩
    rw [← cap_homeomorph_value P ν p,hpx,hxz]
  · rintro ⟨p,hp,he⟩
    refine ⟨@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν))) p,⟨p,hp,rfl⟩,?_⟩
    exact Subtype.ext ((cap_homeomorph_value P ν p).trans he)

def originalCapInteriorChart (P : RawFacePairing T) (ν : Vertex P) (t : T) (j : Fin 4)
    (hc : label P (t,j) = ν) : OpenTriangle ≃ₜ ↥(capInteriorImage P ν (t,j)) :=
  (originalInteriorChart P ν t j hc).trans
    ((actualSliceQuotientHomeomorph P ν).image (quotientInteriorPatch P ν (t,j)))

end D5.S3.Geometry.Gluing.RawFaceInteriorCap1483Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceInteriorCap1483Candidate.cap_interior_image_open,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorCap1483Candidate.cap_homeomorph_value,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorCap1483Candidate.cap_interior_image_representatives,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorCap1483Candidate.originalCapInteriorChart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1483 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1483 disallowed {ax}"
    Lean.logInfo m!"CFMP1483 CHECKED {name} axioms={axioms}"
