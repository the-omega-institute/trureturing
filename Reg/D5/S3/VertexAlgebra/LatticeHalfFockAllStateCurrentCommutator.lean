import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped VertexOperator

noncomputable section

structure CurrentParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  current : Fin lattice.rank → ℂ

structure CurrentState (parameter : CurrentParameters) where
  source : Carrier parameter.lattice
  mode : ℤ
  exponent : ℤ
  vector : ActualTensor parameter.lattice parameter.native

def currentSignature : Signature where
  Params := CurrentParameters
  State := CurrentState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def currentReadout : Realization currentSignature :=
  realize currentSignature (fun _ parameter state =>
    (currentCombination parameter.lattice parameter.native parameter.current state.mode
        ((Ytw parameter.lattice parameter.native state.source).coeff state.exponent state.vector) -
      (Ytw parameter.lattice parameter.native state.source).coeff state.exponent
        (currentCombination parameter.lattice parameter.native parameter.current state.mode state.vector),
      ∑ᶠ degree : ℕ,
        Ring.choose (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.frequency state.mode) degree •
          (Ytw parameter.lattice parameter.native
            (((sourceCurrent parameter.lattice parameter.current)[[(degree : ℤ)]]) state.source)).coeff
            (state.exponent - (2 * state.mode + 1) + 2 * degree) state.vector))
    (fun empty => nomatch empty)

def currentArena : Arena where
  signature := currentSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem currentBridge : (type_of% (@actual_current_Ytw_commutator)) ↔
    currentArena.Law currentReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.current state.source
      state.mode state.exponent state.vector
  · intro law lattice native current source mode exponent vector
    exact law ⟨lattice, native, current⟩ ⟨source, mode, exponent, vector⟩

def currentEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
def currentContinuation : Contract.Continuation Unit := .unknown
abbrev currentRealizationObligation := Registration currentArena
  (type_of% (@actual_current_Ytw_commutator))
abbrev currentContractObligation := Contract.Registration (@actual_current_Ytw_commutator)
  (type_of% currentReadout) (type_of% currentEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator
