import Reg.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedCurrentAction

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedCurrentAction

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedCurrentAction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentCommutator
open LeanInformationAudit

noncomputable section

def correctedReadout : Realization normalSignature :=
  realize normalSignature (fun _ parameter state =>
    (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent parameter.lattice
        (ActualGround parameter.lattice parameter.native) parameter.colour parameter.mode *
        (correctedPolynomial parameter.lattice parameter.native parameter.charge state.1).coeff state.2 -
      (correctedPolynomial parameter.lattice parameter.native parameter.charge state.1).coeff state.2 *
        _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorCurrent parameter.lattice
          (ActualGround parameter.lattice parameter.native) parameter.colour parameter.mode,
      (correctedDelta parameter.lattice parameter.native parameter.charge parameter.colour parameter.mode
        state.1).coeff state.2)) (fun empty => nomatch empty)

def correctedArena : Arena where
  signature := normalSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem correctedBridge : (type_of% (@correctedPolynomial_current_commutator)) ↔
    correctedArena.Law correctedReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.charge parameter.colour parameter.mode
      state.2 state.1
  · intro law lattice native charge colour mode exponent polynomial
    exact law ⟨lattice, native, charge, colour, mode⟩ ⟨polynomial, exponent⟩

def correctedEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.correctedPolynomial
def correctedContinuation : Contract.Continuation Unit := .unknown
abbrev correctedRealizationObligation := Registration correctedArena
  (type_of% (@correctedPolynomial_current_commutator))
abbrev correctedContractObligation := Contract.Registration (@correctedPolynomial_current_commutator)
  (type_of% correctedReadout) (type_of% correctedEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedCurrentAction
