import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumSquare
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
open scoped TensorProduct

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumSquare

noncomputable section

abbrev signature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := Carrier parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def operand (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (matter : Carrier lattice) :
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State lattice :=
  Q lattice matrix
    (matter ⊗ₜ[ℂ] _root_.D5.S3.VertexAlgebra.BcGhostFockSupport.vacuum)

def actual : Realization signature :=
  realize signature (fun _ parameter matter => operand parameter.1 parameter.2 matter)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (_hHG : matrix * gramComplex lattice = 1)
    (_hGH : gramComplex lattice * matrix = 1) (matter : Carrier lattice),
    Q lattice matrix (readout.readout () ⟨lattice, matrix⟩ matter) = 0

def sourceStatement : Prop :=
  ∀ (lattice : LatticeData) (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (_hHG : matrix * gramComplex lattice = 1)
    (_hGH : gramComplex lattice * matrix = 1) (matter : Carrier lattice),
    (Q lattice matrix * Q lattice matrix)
      (matter ⊗ₜ[ℂ] _root_.D5.S3.VertexAlgebra.BcGhostFockSupport.vacuum) = 0

theorem sourceReconstruction : sourceStatement ↔ arena.Law actual := Iff.rfl

theorem exactTarget : sourceStatement :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumSquare.vacuum_square

theorem actualPositive : arena.Law actual := sourceReconstruction.mp exactTarget

#print axioms sourceReconstruction
#print axioms exactTarget
#print axioms actualPositive

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumSquare
