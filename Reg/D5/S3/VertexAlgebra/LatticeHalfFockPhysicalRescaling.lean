import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  determinant : IsUnit lattice.G.det
  charge : Charge lattice
  word : List (Index lattice)

def reconstructionSignature : Signature where
  Params := Parameters
  State parameter := ℤ × ActualTensor parameter.lattice parameter.determinant
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.determinant ×
    ActualTensor parameter.lattice parameter.determinant
  Anchor := Empty
  finiteAnchor := inferInstance

def reconstructionReadout : Realization reconstructionSignature :=
  realize reconstructionSignature (fun _ parameter state =>
    ((normalWord parameter.lattice parameter.determinant parameter.charge parameter.word).coeff
        state.1 state.2,
      (physicalLift parameter.lattice parameter.determinant
        (physicalWord parameter.lattice parameter.determinant parameter.charge 0 parameter.word)
        (wordShift parameter.lattice parameter.word) +
       physicalLift parameter.lattice parameter.determinant
        (physicalWord parameter.lattice parameter.determinant parameter.charge 1 parameter.word)
        (wordShift parameter.lattice parameter.word + 1)).coeff state.1 state.2))
    (fun empty => nomatch empty)

def reconstructionArena : Arena where
  signature := reconstructionSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem reconstructionBridge : (type_of% (@normalWord_physical_reconstruction)) ↔
    reconstructionArena.Law reconstructionReadout := by
  constructor
  · intro source parameter state
    exact congrArg (fun field : NativeField parameter.lattice parameter.determinant =>
      field.coeff state.1 state.2)
        (source parameter.lattice parameter.determinant parameter.charge parameter.word)
  · intro law lattice determinant charge word
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    exact law ⟨lattice, determinant, charge, word⟩ ⟨exponent, vector⟩

def reconstructionEscapeFrom :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalWord
def reconstructionContinuation : Contract.Continuation Unit := .unknown
abbrev reconstructionRealizationObligation :=
  Registration reconstructionArena (type_of% (@normalWord_physical_reconstruction))
abbrev reconstructionContractObligation := Contract.Registration (@normalWord_physical_reconstruction)
  (type_of% reconstructionReadout) (type_of% reconstructionEscapeFrom) Unit
abbrev insertionContractObligation := Contract.Registration (@physicalSlice_normalInsertion)
  (type_of% reconstructionReadout) (type_of% reconstructionEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
