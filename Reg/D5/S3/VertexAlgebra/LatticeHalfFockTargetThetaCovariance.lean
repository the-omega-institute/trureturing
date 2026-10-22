import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCovariance

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCovariance

open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockLZeroCovariance
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
  source : Carrier parameter.lattice
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
    (LatticeHalfFock.tensorL parameter.lattice (ActualGround parameter.lattice parameter.native) parameter.matrixH 0 ((Ytw parameter.lattice parameter.native state.source).coeff state.exponent state.vector),
     (Ytw parameter.lattice parameter.native state.source).coeff state.exponent (LatticeHalfFock.tensorL parameter.lattice (ActualGround parameter.lattice parameter.native) parameter.matrixH 0 state.vector) +
      (Ytw parameter.lattice parameter.native
        (sugawaraMode parameter.lattice parameter.matrixH 0 state.source)).coeff
          state.exponent state.vector + ((state.exponent : ℂ) / 2) •
            (Ytw parameter.lattice parameter.native state.source).coeff state.exponent state.vector))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem bridge : (type_of% (@Ytw_L0_covariance)) ↔ arena.Law readout := by
  constructor
  · intro theoremProof parameter state
    exact theoremProof parameter.lattice parameter.native parameter.matrixH parameter.hHG parameter.hGH state.source state.exponent state.vector
  · intro law lattice native matrixH hHG hGH source exponent vector
    exact law ⟨lattice, native, matrixH, hHG, hGH⟩ ⟨source, exponent, vector⟩

def escapeFrom := @Ytw
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@Ytw_L0_covariance))
abbrev contractObligation := Contract.Registration (@Ytw_L0_covariance)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCovariance
