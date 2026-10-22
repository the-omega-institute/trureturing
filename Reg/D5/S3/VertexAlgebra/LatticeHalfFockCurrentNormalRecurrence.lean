import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormalRecurrence

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormalRecurrence

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormalRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure InsertionParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  colour : Fin lattice.rank
  mode : ℤ
  index : Index lattice
  field : NativeField lattice native
  deltaField : NativeField lattice native
  commutator : ∀ coefficient : ℤ,
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent lattice (ActualGround lattice native)
        colour mode * field.coeff coefficient -
      field.coeff coefficient * _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent lattice
        (ActualGround lattice native) colour mode = deltaField.coeff coefficient

def insertionSignature : Signature where
  Params := InsertionParameters
  State parameter := ℤ × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def insertionReadout : Realization insertionSignature :=
  realize insertionSignature (fun _ parameter state =>
    (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent parameter.lattice
        (ActualGround parameter.lattice parameter.native) parameter.colour parameter.mode
        ((normalInsertion parameter.lattice parameter.native parameter.index parameter.field).coeff
          state.1 state.2) -
      (normalInsertion parameter.lattice parameter.native parameter.index parameter.field).coeff state.1
        (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent parameter.lattice
          (ActualGround parameter.lattice parameter.native) parameter.colour parameter.mode state.2),
      (normalInsertion parameter.lattice parameter.native parameter.index parameter.deltaField).coeff
        state.1 state.2 +
      (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.frequency parameter.mode *
        jetScalar parameter.index.2 (-parameter.mode - 1) *
        (parameter.lattice.G parameter.colour parameter.index.1 : ℂ)) •
          parameter.field.coeff
            (state.1 - 2 * parameter.mode + 2 * parameter.index.2 + 1) state.2))
    (fun empty => nomatch empty)

def insertionArena : Arena where
  signature := insertionSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem insertionBridge : (type_of% (@normalInsertion_current_commutator)) ↔
    insertionArena.Law insertionReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.colour parameter.mode state.1
      parameter.index parameter.field parameter.deltaField parameter.commutator state.2
  · intro law lattice native colour mode exponent index field deltaField commutator vector
    exact law ⟨lattice, native, colour, mode, index, field, deltaField, commutator⟩ ⟨exponent, vector⟩

def insertionEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalInsertion
def insertionContinuation : Contract.Continuation Unit := .unknown
abbrev insertionRealizationObligation := Registration insertionArena
  (type_of% (@normalInsertion_current_commutator))
abbrev insertionContractObligation := Contract.Registration (@normalInsertion_current_commutator)
  (type_of% insertionReadout) (type_of% insertionEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormalRecurrence
