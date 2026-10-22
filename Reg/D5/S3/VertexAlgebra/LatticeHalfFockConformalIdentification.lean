import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure ConformalParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftInverse : inverse *
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.gramComplex lattice = 1

def conformalSignature : Signature where
  Params := ConformalParameters
  State parameter := ℤ × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def conformalReadout : Realization conformalSignature :=
  realize conformalSignature (fun _ parameter source =>
    ((_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
      parameter.lattice parameter.native
      (_root_.D5.S3.VertexAlgebra.LatticeActualConformalState.omega
        parameter.lattice parameter.inverse)).coeff source.1 source.2,
      (_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorStressField parameter.lattice
        (ActualGround parameter.lattice parameter.native) parameter.inverse).coeff
          source.1 source.2)) (fun empty => nomatch empty)

def conformalArena : Arena where
  signature := conformalSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem conformalBridge : (type_of% (@Ytw_omega)) ↔ conformalArena.Law conformalReadout := by
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

def conformalEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
def conformalContinuation : Contract.Continuation Unit := .unknown
abbrev conformalRealizationObligation :=
  Registration conformalArena (type_of% (@Ytw_omega))
abbrev conformalContractObligation := Contract.Registration (@Ytw_omega)
  (type_of% conformalReadout) (type_of% conformalEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification
