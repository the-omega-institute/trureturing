import Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Grading

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Grading

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

structure GradingParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det

def gradingSignature : Signature where
  Params := GradingParameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def gradingReadout : Realization gradingSignature :=
  realize gradingSignature (fun _ parameter state =>
    (∑ level ∈ supportedLevels parameter.lattice parameter.native state,
      naturalProjector parameter.lattice parameter.native level state, state)) (fun empty => nomatch empty)

def gradingArena : Arena where
  signature := gradingSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem gradingBridge : (type_of% (@finite_reconstruction)) ↔ gradingArena.Law gradingReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native state
  · intro law lattice native state
    exact law ⟨lattice, native⟩ state

def gradingEscapeFrom := @naturalProjector
def gradingContinuation : Contract.Continuation Unit := .unknown
abbrev gradingRegistrationObligation := Registration gradingArena (type_of% (@finite_reconstruction))
abbrev gradingContractObligation := Contract.Registration (@finite_reconstruction)
  (type_of% gradingReadout) (type_of% gradingEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Grading
