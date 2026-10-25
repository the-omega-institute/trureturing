import CFMPGenericCoordinateTopology1254Transient
import CFMPGenericActualSeam1276Transient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate (OrderedEnd Component LocalNoEdgeReversal)
open D5.S3.Geometry.Gluing.RawFaceCycleCandidate (Orientation)
open D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate (sectorCount enumeration)
open D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate
  (Neighborhood PointQuotient quotientNeighborhood actual_open_quotient_neighborhood)
open D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate
  (Phi sectorCount_neZero actual_eqvgen_iff)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (Sector seam closedInput OpenDisk)
open private closed_chain_restriction strictFanDiskHomeomorph
  from D5.S3.Geometry.Gluing.ActualLinkAffineFan
variable {T : Type*} [Fintype T]

-- Uncompiled temporary composition; existing disk and original quotient are reused.
theorem actual_full_fan_correspondence (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (z w : Fin (sectorCount P d0) × Sector) :
    Related P (Phi P s d0 hNR z).val (Phi P s d0 hNR w).val ↔
      CyclicTriangleDisk.Related (closedInput z) (closedInput w) :=
  (actual_eqvgen_iff P s d0 hNR z w).trans (closed_chain_restriction z w).symm

section Topology
variable [TopologicalSpace T] [DiscreteTopology T]

-- Use exactly the induced instances selected in the compiled component topology source.
local instance componentTopology (P : RawFacePairing T) (d0 : OrderedEnd T) :
    TopologicalSpace (Component P d0) :=
  D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate.componentTopology P d0

local instance componentDiscrete (P : RawFacePairing T) (d0 : OrderedEnd T) :
    DiscreteTopology (Component P d0) :=
  D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate.componentDiscrete P d0

def enumerationHomeomorph (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) :
    Fin (sectorCount P d0) ≃ₜ Component P d0 where
  toEquiv := enumeration P s d0 hNR
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- Both directions use the inherited original component and strict-neighborhood topology. -/
def indexedCoordinateHomeomorph (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) :
    (Fin (sectorCount P d0) × Sector) ≃ₜ
      ↥(Neighborhood P (ν := label P d0.val.1) d0.val) :=
  ((enumerationHomeomorph P s d0 hNR).prodCongr (Homeomorph.refl Sector)).trans
    (D5.S3.Geometry.Gluing.RawFaceCoordinateTopologyCandidate.coordinateHomeomorph
      P s.reversed d0)

theorem indexedCoordinateHomeomorph_apply (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (z : Fin (sectorCount P d0) × Sector) :
    indexedCoordinateHomeomorph P s d0 hNR z = Phi P s d0 hNR z := rfl

/-- The codomain is the open image in the full original quotient, with subspace topology. -/
def actualSeamQuotientHomeomorph (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) :
    Quotient (Relation.EqvGen.setoid (@seam (sectorCount P d0) _)) ≃ₜ
      ↥(quotientNeighborhood P (ν := label P d0.val.1) d0.val) := by
  let q : Point P (label P d0.val.1) → PointQuotient P (label P d0.val.1) :=
    @Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := label P d0.val.1)))
  let N : Set (Point P (label P d0.val.1)) :=
    Neighborhood P (ν := label P d0.val.1) d0.val
  let U : Set (PointQuotient P (label P d0.val.1)) :=
    quotientNeighborhood P (ν := label P d0.val.1) d0.val
  have hs : q ⁻¹' U = N := (actual_open_quotient_neighborhood P d0.val).1
  let e : ↥N ≃ₜ ↥(q ⁻¹' U) := Homeomorph.setCongr hs.symm
  let f : (Fin (sectorCount P d0) × Sector) → ↥U :=
    U.restrictPreimage q ∘ e ∘ indexedCoordinateHomeomorph P s d0 hNR
  have hf : Topology.IsQuotientMap f :=
    (actual_open_quotient_neighborhood P d0.val).2.2.comp
      (e.isQuotientMap.comp (indexedCoordinateHomeomorph P s d0 hNR).isQuotientMap)
  have hv (z : Fin (sectorCount P d0) × Sector) :
      (f z).val = q (Phi P s d0 hNR z).val := rfl
  have hk : ∀ z w : Fin (sectorCount P d0) × Sector,
      Relation.EqvGen seam z w ↔ f z = f w := by
    intro z w
    have hr := actual_eqvgen_iff P s d0 hNR z w
    constructor
    · intro h
      have hq : q (Phi P s d0 hNR z).val = q (Phi P s d0 hNR w).val :=
        Quotient.sound (hr.mpr h)
      exact Subtype.ext ((hv z).trans (hq.trans (hv w).symm))
    · intro h
      have hq : q (Phi P s d0 hNR z).val = q (Phi P s d0 hNR w).val :=
        (hv z).symm.trans ((congrArg (fun t : ↥U => t.val) h).trans (hv w))
      exact hr.mp (Quotient.exact hq)
  let fC : C(Fin (sectorCount P d0) × Sector, ↥U) := ⟨f,hf.continuous⟩
  exact (Homeomorph.Quotient.congrRight hk).trans
    (Topology.IsQuotientMap.homeomorph (f := fC) hf)

/-- Existing strict-fan disk theorem supplies the continuous inverse for every positive m. -/
def actualOpenDiskChart (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) :
    ↥(quotientNeighborhood P (ν := label P d0.val.1) d0.val) ≃ₜ OpenDisk :=
  (actualSeamQuotientHomeomorph P s d0 hNR).symm.trans
    (strictFanDiskHomeomorph (n := sectorCount P d0))
end Topology
end D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate.actual_full_fan_correspondence,
      ``D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate.enumerationHomeomorph,
      ``D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate.indexedCoordinateHomeomorph,
      ``D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate.indexedCoordinateHomeomorph_apply,
      ``D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate.actualSeamQuotientHomeomorph,
      ``D5.S3.Geometry.Gluing.RawFaceIndexedQuotientDiskCandidate.actualOpenDiskChart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1291 original quotient disk target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1291 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1291 CHECKED {name} axioms={axioms}"
