import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance

noncomputable section

abbrev signature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := ℤ × _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def operand (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (input : ℤ × _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State lattice) :
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State lattice :=
  Q lattice matrix input.2

def actual : Realization signature :=
  realize signature (fun _ parameter input => operand parameter.1 parameter.2 input)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (_hHG : matrix * gramComplex lattice = 1)
    (_hGH : gramComplex lattice * matrix = 1) (mode : ℤ)
    (psi : _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State lattice),
    readout.readout () ⟨lattice, matrix⟩
        (mode, (M lattice matrix mode + G lattice mode) psi) -
      (M lattice matrix mode + G lattice mode)
        (readout.readout () ⟨lattice, matrix⟩ (mode, psi)) =
      -((((lattice.rank : ℂ) - 26) / 12) * ((mode : ℂ) ^ 3 - (mode : ℂ))) • C lattice mode psi

def sourceStatement : Prop :=
  ∀ (lattice : LatticeData) (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (_hHG : matrix * gramComplex lattice = 1)
    (_hGH : gramComplex lattice * matrix = 1) (mode : ℤ),
    Q lattice matrix * (M lattice matrix mode + G lattice mode) -
      (M lattice matrix mode + G lattice mode) * Q lattice matrix =
      -((((lattice.rank : ℂ) - 26) / 12) * ((mode : ℂ) ^ 3 - (mode : ℂ))) • C lattice mode

theorem sourceReconstruction : sourceStatement ↔ arena.Law actual := by
  constructor
  · intro h lattice matrix hHG hGH mode psi
    have heq := congrArg
      (fun operator : Module.End ℂ
        (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State lattice) => operator psi)
      (h lattice matrix hHG hGH mode)
    change Q lattice matrix ((M lattice matrix mode + G lattice mode) psi) -
      (M lattice matrix mode + G lattice mode) (Q lattice matrix psi) = _
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] using heq
  · intro h lattice matrix hHG hGH mode
    apply LinearMap.ext
    intro psi
    have heq := h lattice matrix hHG hGH mode psi
    change Q lattice matrix ((M lattice matrix mode + G lattice mode) psi) -
      (M lattice matrix mode + G lattice mode) (Q lattice matrix psi) = _ at heq
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] using heq

theorem exactTarget : sourceStatement :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance.total_covariance

theorem actualPositive : arena.Law actual := sourceReconstruction.mp exactTarget

#print axioms sourceReconstruction
#print axioms exactTarget
#print axioms actualPositive

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance
