import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalMixedIterate
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators VertexOperator

noncomputable section

structure SeedParameters where
  lattice : LatticeData
  unitDeterminant : IsUnit lattice.G.det
  current : Fin lattice.rank → ℂ

def seedSignature : Signature where
  Params := SeedParameters
  State parameter := Carrier parameter.lattice ×
    ActualTensor parameter.lattice parameter.unitDeterminant × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.unitDeterminant ×
    ActualTensor parameter.lattice parameter.unitDeterminant
  Anchor := Empty
  finiteAnchor := inferInstance

def seedReadout : Realization seedSignature :=
  realize seedSignature (fun _ parameter state =>
    ((Ytw parameter.lattice parameter.unitDeterminant
        (((sourceCurrent parameter.lattice parameter.current)[[-1]]) state.1)).coeff
          state.2.2 state.2.1 +
      ∑ᶠ degree : ℕ, Ring.choose (1 / 2 : ℂ) (degree + 1) •
        (Ytw parameter.lattice parameter.unitDeterminant
          (((sourceCurrent parameter.lattice parameter.current)[[(degree : ℤ)]]) state.1)).coeff
            (state.2.2 + 2 * degree + 2) state.2.1,
      ∑ colour, parameter.current colour •
        (normalInsertion parameter.lattice parameter.unitDeterminant (colour, 0)
          (Ytw parameter.lattice parameter.unitDeterminant state.1)).coeff state.2.2 state.2.1))
    (fun empty => nomatch empty)

def seedArena : Arena where
  signature := seedSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem seedBridge : (type_of% (@actual_current_seed)) ↔ seedArena.Law seedReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.unitDeterminant parameter.current
      state.1 state.2.1 state.2.2
  · intro law lattice unitDeterminant current state vector exponent
    exact law ⟨lattice, unitDeterminant, current⟩ ⟨state, vector, exponent⟩

def seedEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
def seedContinuation : Contract.Continuation Unit := .unknown
abbrev seedRealizationObligation := Registration seedArena (type_of% (@actual_current_seed))
abbrev seedContractObligation := Contract.Registration (@actual_current_seed)
  (type_of% seedReadout) (type_of% seedEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeedConstruction
