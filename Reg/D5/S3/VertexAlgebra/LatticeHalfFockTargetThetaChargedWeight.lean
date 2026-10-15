import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaChargedWeight

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaChargedWeight

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockAllStateField LatticeHalfFockFiniteCorrection
open LatticeSugawaraConformal LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  matrixH : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  hHG : matrixH * LatticeSugawaraCurrents.gramComplex lattice = 1
  hGH : LatticeSugawaraCurrents.gramComplex lattice * matrixH = 1

structure State (parameter : Parameters) where
  charge : Charge parameter.lattice
  exponent : ℤ
  vector : ActualTensor parameter.lattice parameter.native

def signature : Signature where
  Params := Parameters
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    (LatticeHalfFock.tensorL parameter.lattice (ActualGround parameter.lattice parameter.native) parameter.matrixH 0 (chargedCoefficient parameter.lattice parameter.native state.charge state.exponent state.vector),
     chargedCoefficient parameter.lattice parameter.native state.charge state.exponent (LatticeHalfFock.tensorL parameter.lattice (ActualGround parameter.lattice parameter.native) parameter.matrixH 0 state.vector) +
      (((state.exponent + chargeNorm parameter.lattice state.charge : ℤ) : ℂ) / 2) •
      chargedCoefficient parameter.lattice parameter.native state.charge state.exponent state.vector)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem bridge : (type_of% (@charged_tensor_L0_covariance)) ↔ arena.Law readout := by
  constructor
  · intro theoremProof parameter state
    exact theoremProof parameter.lattice parameter.native parameter.matrixH parameter.hHG parameter.hGH state.charge state.exponent state.vector
  · intro law lattice native matrixH hHG hGH charge exponent vector
    exact law ⟨lattice, native, matrixH, hHG, hGH⟩ ⟨charge, exponent, vector⟩

def escapeFrom := @chargedCoefficient
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@charged_tensor_L0_covariance))
abbrev contractObligation := Contract.Registration (@charged_tensor_L0_covariance)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaChargedWeight
