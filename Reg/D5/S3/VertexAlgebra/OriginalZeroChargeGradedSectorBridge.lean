import D5.S3.VertexAlgebra.OriginalZeroChargeGradedSectorBridge
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalZeroChargeGradedSectorBridge

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalZeroChargeGradedSectorBridge OriginalQQuartetSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure SectorParameters where
  lattice : LatticeData
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGram : inverse * gramComplex lattice = 1
  rightGram : gramComplex lattice * inverse = 1

def sectorSignature : Signature where
  Params := SectorParameters
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Submodule ℂ (State parameter.lattice) ×
    Submodule ℂ (State parameter.lattice)
  Anchor := Empty
  finiteAnchor := inferInstance

def sectorReadout : Realization sectorSignature :=
  realize sectorSignature (fun _ parameter _ =>
    (OriginalZeroChargeEnergyBasis.sector parameter.lattice,
      originalEnergySector parameter.lattice parameter.inverse 0 1))
    (fun empty => nomatch empty)

def sectorArena : Arena where
  signature := sectorSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem sectorSourceBridge : (type_of% (@sector_eq_original)) ↔ sectorArena.Law sectorReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.inverse parameter.leftGram parameter.rightGram
  · intro law lattice inverse leftGram rightGram
    exact law ⟨lattice, inverse, leftGram, rightGram⟩ ()

abbrev BoundaryTarget := type_of% (@boundary_correspondence)
abbrev ForwardRepresentativeTarget := type_of% (@cohomologyEquiv_representative)
abbrev InverseRepresentativeTarget := type_of% (@cohomologyEquiv_inverse_representative)
abbrev NumberTarget := type_of% (@cohomologyEquiv_number)
abbrev GradedInclusionTarget := type_of% (@gradedEquiv_inclusion)
abbrev PredecessorTarget := type_of% (@ghost_predecessor_preimage)
abbrev GradedDimensionTarget := type_of% (@original_zero_graded_finrank)
abbrev FullDimensionTarget := type_of% (@original_zero_finrank)

theorem boundarySourceBridge : (type_of% (@boundary_correspondence)) ↔ BoundaryTarget := Iff.rfl
theorem forwardSourceBridge : (type_of% (@cohomologyEquiv_representative)) ↔
    ForwardRepresentativeTarget := Iff.rfl
theorem inverseSourceBridge : (type_of% (@cohomologyEquiv_inverse_representative)) ↔
    InverseRepresentativeTarget := Iff.rfl
theorem numberSourceBridge : (type_of% (@cohomologyEquiv_number)) ↔ NumberTarget := Iff.rfl
theorem gradedSourceBridge : (type_of% (@gradedEquiv_inclusion)) ↔ GradedInclusionTarget := Iff.rfl
theorem predecessorSourceBridge : (type_of% (@ghost_predecessor_preimage)) ↔
    PredecessorTarget := Iff.rfl
theorem gradedDimensionSourceBridge : (type_of% (@original_zero_graded_finrank)) ↔
    GradedDimensionTarget := Iff.rfl
theorem fullDimensionSourceBridge : (type_of% (@original_zero_finrank)) ↔
    FullDimensionTarget := Iff.rfl

abbrev sectorRealizationObligation := Registration sectorArena (type_of% (@sector_eq_original))
abbrev sectorContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@sector_eq_original)
    (type_of% sectorReadout) (PLift (type_of% (@boundary_correspondence))) Unit

theorem sector_dependence_impossible :
    ¬ ObservationalDependence sectorSignature sectorReadout := by
  intro dependence
  obtain ⟨parameter, first, second, different⟩ := dependence ()
  exact different (by cases first; cases second; rfl)

theorem sector_registration_impossible (registration : sectorRealizationObligation) : False := by
  obtain ⟨parameter, first, second, different⟩ := registration.dependence ()
  exact different (by cases first; cases second; rfl)

end
end Reg.D5.S3.VertexAlgebra.OriginalZeroChargeGradedSectorBridge
