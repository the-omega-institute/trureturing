import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockLZeroCovariance

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockLZeroCovariance

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockLZeroCovariance
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftInverse : inverse * gramComplex lattice = 1
  rightInverse : gramComplex lattice * inverse = 1

def normalSignature : Signature where
  Params := Parameters
  State parameter := Charge parameter.lattice × List (Index parameter.lattice) ×
    ℤ × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def normalReadout : Realization normalSignature :=
  realize normalSignature (fun _ parameter source =>
    ((_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorL parameter.lattice
        (ActualGround parameter.lattice parameter.native) parameter.inverse 0)
      ((normalWord parameter.lattice parameter.native source.1 source.2.1).coeff
        source.2.2.1 source.2.2.2),
      (normalWord parameter.lattice parameter.native source.1 source.2.1).coeff source.2.2.1
        ((_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorL parameter.lattice
          (ActualGround parameter.lattice parameter.native) parameter.inverse 0) source.2.2.2) +
        ((wordWeight parameter.lattice source.2.1 : ℂ) +
          ((source.2.2.1 + chargeNorm parameter.lattice source.1 : ℤ) : ℂ) / 2) •
          (normalWord parameter.lattice parameter.native source.1 source.2.1).coeff
            source.2.2.1 source.2.2.2)) (fun empty => nomatch empty)

def normalArena : Arena where
  signature := normalSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem normalBridge : (type_of% (@normalWord_L0)) ↔ normalArena.Law normalReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.inverse
      parameter.leftInverse parameter.rightInverse state.1 state.2.1 state.2.2.1 state.2.2.2
  · intro law lattice native inverse leftInverse rightInverse charge word exponent vector
    exact law ⟨lattice, native, inverse, leftInverse, rightInverse⟩ ⟨charge, word, exponent, vector⟩

def covarianceSignature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice × ℤ × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def covarianceReadout : Realization covarianceSignature :=
  realize covarianceSignature (fun _ parameter source =>
    ((_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorL parameter.lattice
        (ActualGround parameter.lattice parameter.native) parameter.inverse 0)
      ((Ytw parameter.lattice parameter.native source.1).coeff source.2.1 source.2.2),
      (Ytw parameter.lattice parameter.native source.1).coeff source.2.1
        ((_root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorL parameter.lattice
          (ActualGround parameter.lattice parameter.native) parameter.inverse 0) source.2.2) +
      (Ytw parameter.lattice parameter.native
        (sugawaraMode parameter.lattice parameter.inverse 0 source.1)).coeff source.2.1 source.2.2 +
      ((source.2.1 : ℂ) / 2) •
        (Ytw parameter.lattice parameter.native source.1).coeff source.2.1 source.2.2))
    (fun empty => nomatch empty)

def covarianceArena : Arena where
  signature := covarianceSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem covarianceBridge : (type_of% (@Ytw_L0_covariance)) ↔
    covarianceArena.Law covarianceReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.inverse
      parameter.leftInverse parameter.rightInverse state.1 state.2.1 state.2.2
  · intro law lattice native inverse leftInverse rightInverse source exponent vector
    exact law ⟨lattice, native, inverse, leftInverse, rightInverse⟩ ⟨source, exponent, vector⟩

def homogeneousSignature : Signature where
  Params := Parameters
  State parameter := {state : Carrier parameter.lattice × ℂ × ℂ × ℤ ×
      ActualTensor parameter.lattice parameter.native //
    sugawaraMode parameter.lattice parameter.inverse 0 state.1 = state.2.1 • state.1 ∧
    _root_.D5.S3.VertexAlgebra.LatticeHalfFock.tensorL parameter.lattice
      (ActualGround parameter.lattice parameter.native) parameter.inverse 0 state.2.2.2.2 =
        state.2.2.1 • state.2.2.2.2}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def homogeneousReadout : Realization homogeneousSignature :=
  realize homogeneousSignature (fun _ parameter source =>
    ((Ytw parameter.lattice parameter.native
      (_root_.D5.S3.VertexAlgebra.LatticeActualConformalState.omega
        parameter.lattice parameter.inverse)).coeff (-4)
        ((Ytw parameter.lattice parameter.native source.val.1).coeff
          source.val.2.2.2.1 source.val.2.2.2.2),
      (source.val.2.2.1 + source.val.2.1 + (source.val.2.2.2.1 : ℂ) / 2) •
        (Ytw parameter.lattice parameter.native source.val.1).coeff
          source.val.2.2.2.1 source.val.2.2.2.2)) (fun empty => nomatch empty)

def homogeneousArena : Arena where
  signature := homogeneousSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem homogeneousBridge : (type_of% (@Ytw_homogeneous_coefficient)) ↔
    homogeneousArena.Law homogeneousReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.inverse
      parameter.leftInverse parameter.rightInverse state.val.1 state.val.2.1 state.val.2.2.1
      state.property.1 state.val.2.2.2.1 state.val.2.2.2.2 state.property.2
  · intro law lattice native inverse leftInverse rightInverse source sourceEnergy targetEnergy
      sourceHomogeneous exponent vector targetHomogeneous
    exact law ⟨lattice, native, inverse, leftInverse, rightInverse⟩
      ⟨⟨source, sourceEnergy, targetEnergy, exponent, vector⟩,
        sourceHomogeneous, targetHomogeneous⟩

def covarianceEscapeFrom := @Ytw
def covarianceContinuation : Contract.Continuation Unit := .unknown

abbrev normalRealizationObligation := Registration normalArena (type_of% (@normalWord_L0))
abbrev normalContractObligation := Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@normalWord_L0)
  (type_of% normalReadout) (type_of% covarianceEscapeFrom) Unit
abbrev covarianceRealizationObligation :=
  Registration covarianceArena (type_of% (@Ytw_L0_covariance))
abbrev covarianceContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@Ytw_L0_covariance)
  (type_of% covarianceReadout) (type_of% covarianceEscapeFrom) Unit
abbrev homogeneousRealizationObligation :=
  Registration homogeneousArena (type_of% (@Ytw_homogeneous_coefficient))
abbrev homogeneousContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@Ytw_homogeneous_coefficient)
    (type_of% homogeneousReadout) (type_of% covarianceEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockLZeroCovariance
