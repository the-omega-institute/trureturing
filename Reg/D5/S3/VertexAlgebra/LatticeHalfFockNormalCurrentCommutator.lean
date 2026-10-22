import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure NormalParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice
  colour : Fin lattice.rank
  mode : ℤ

def normalSignature : Signature where
  Params := NormalParameters
  State parameter := Oscillator parameter.lattice × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Module.End ℂ (ActualTensor parameter.lattice parameter.native) ×
    Module.End ℂ (ActualTensor parameter.lattice parameter.native)
  Anchor := Empty
  finiteAnchor := inferInstance

def normalReadout : Realization normalSignature :=
  realize normalSignature (fun _ parameter state =>
    (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent parameter.lattice
        (ActualGround parameter.lattice parameter.native) parameter.colour parameter.mode *
        (normalPolynomial parameter.lattice parameter.native parameter.charge state.1).coeff state.2 -
      (normalPolynomial parameter.lattice parameter.native parameter.charge state.1).coeff state.2 *
        _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent parameter.lattice
          (ActualGround parameter.lattice parameter.native) parameter.colour parameter.mode,
      (nativeDelta parameter.lattice parameter.native parameter.charge parameter.colour parameter.mode
        state.1).coeff state.2)) (fun empty => nomatch empty)

def normalArena : Arena where
  signature := normalSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem normalBridge : (type_of% (@normalPolynomial_current_commutator)) ↔
    normalArena.Law normalReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.charge parameter.colour parameter.mode
      state.1 state.2
  · intro law lattice native charge colour mode polynomial exponent
    exact law ⟨lattice, native, charge, colour, mode⟩ ⟨polynomial, exponent⟩

def normalEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalPolynomial
def normalContinuation : Contract.Continuation Unit := .unknown
abbrev normalRealizationObligation := Registration normalArena
  (type_of% (@normalPolynomial_current_commutator))
abbrev normalContractObligation := Contract.Registration (@normalPolynomial_current_commutator)
  (type_of% normalReadout) (type_of% normalEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator
