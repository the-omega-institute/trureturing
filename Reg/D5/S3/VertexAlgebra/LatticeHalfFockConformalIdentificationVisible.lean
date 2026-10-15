import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentificationVisible

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentificationVisible

open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeActualConformalState
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentificationVisible
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftInverse : inverse *
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.gramComplex lattice = 1

def signature : Signature where
  Params := Parameters
  State parameter := ℤ × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    ((_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
      parameter.lattice parameter.native
      (_root_.D5.S3.VertexAlgebra.LatticeActualConformalState.omega
        parameter.lattice parameter.inverse)).coeff state.1 state.2,
      (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorStressField parameter.lattice
        (ActualGround parameter.lattice parameter.native) parameter.inverse).coeff
          state.1 state.2)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem bridge : (type_of% (@Ytw_omega)) ↔ arena.Law readout := by
  constructor
  · intro source parameter state
    exact congrArg (fun field => field.coeff state.1 state.2)
      (source parameter.lattice parameter.native parameter.inverse parameter.leftInverse)
  · intro law lattice native inverse leftInverse
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    exact law ⟨lattice, native, inverse, leftInverse⟩ ⟨exponent, vector⟩

def escapeFrom := @Ytw
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@Ytw_omega))
abbrev contractObligation := Contract.Registration (@Ytw_omega)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentificationVisible
