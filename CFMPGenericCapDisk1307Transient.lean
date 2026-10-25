import CFMPGenericIndexedQuotientDisk1291Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceCapDiskCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate (OrderedEnd LocalNoEdgeReversal)
open D5.S3.Geometry.Gluing.RawFaceCycleCandidate (Orientation)
open D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate
  (quotientNeighborhood actual_open_quotient_neighborhood)
open D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate (actualOpenDiskChart)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (OpenDisk)
variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

/-- Relative open image in the original full cap quotient subspace. -/
def capStrictImage (P : RawFacePairing T) (d0 : OrderedEnd T) :
    Set ↥(quotientSlice P (label P d0.val.1)) :=
  (actualSliceQuotientHomeomorph P (label P d0.val.1)) ''
    quotientNeighborhood P (ν := label P d0.val.1) d0.val

theorem cap_homeomorph_value (P : RawFacePairing T) (d0 : OrderedEnd T)
    (p : Point P (label P d0.val.1)) :
    ((actualSliceQuotientHomeomorph P (label P d0.val.1)) (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := label P d0.val.1))) p)).val =
      (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P)) (toTruncation P p) : TruncatedQuotient P) := by
  rfl

theorem cap_strict_image_open (P : RawFacePairing T) (d0 : OrderedEnd T) :
    IsOpen (capStrictImage P d0) :=
  (actualSliceQuotientHomeomorph P (label P d0.val.1)).isOpen_image.mpr
    (actual_open_quotient_neighborhood P d0.val).2.1

theorem cap_strict_image_representatives (P : RawFacePairing T) (d0 : OrderedEnd T)
    (z : ↥(quotientSlice P (label P d0.val.1))) :
    z ∈ capStrictImage P d0 ↔
      ∃ p : Point P (label P d0.val.1),
        p ∈ D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate.Neighborhood P d0.val ∧
        (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P)) (toTruncation P p) : TruncatedQuotient P) = z.val := by
  constructor
  · rintro ⟨x,⟨p,hp,hpx⟩,hxz⟩
    refine ⟨p,hp,?_⟩
    rw [← cap_homeomorph_value P d0 p,hpx,hxz]
  · rintro ⟨p,hp,he⟩
    refine ⟨@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := label P d0.val.1))) p,⟨p,hp,rfl⟩,?_⟩
    exact Subtype.ext ((cap_homeomorph_value P d0 p).trans he)

/-- Openness is relative to the actual cap image, not the full 3D quotient. -/
def actualCapDiskChart (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) :
    ↥(capStrictImage P d0) ≃ₜ OpenDisk :=
  ((actualSliceQuotientHomeomorph P (label P d0.val.1)).image
    (quotientNeighborhood P (ν := label P d0.val.1) d0.val)).symm.trans
      (actualOpenDiskChart P s d0 hNR)
end D5.S3.Geometry.Gluing.RawFaceCapDiskCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCapDiskCandidate.cap_homeomorph_value,
      ``D5.S3.Geometry.Gluing.RawFaceCapDiskCandidate.cap_strict_image_open,
      ``D5.S3.Geometry.Gluing.RawFaceCapDiskCandidate.cap_strict_image_representatives,
      ``D5.S3.Geometry.Gluing.RawFaceCapDiskCandidate.actualCapDiskChart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1307 cap transport target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1307 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1307 CHECKED {name} axioms={axioms}"
