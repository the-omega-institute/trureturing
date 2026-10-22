import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence

noncomputable section

abbrev signature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def operand (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ) (state : State lattice) :
    State lattice := Q lattice matrix state

def actual : Realization signature :=
  realize signature (fun _ parameter state => operand parameter.1 parameter.2 state)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (_hHG : matrix * gramComplex lattice = 1)
    (_hGH : gramComplex lattice * matrix = 1) (_hcritical : lattice.rank = 26)
    (state : State lattice),
    Q lattice matrix (readout.readout () ⟨lattice, matrix⟩ state) = 0

def sourceStatement : Prop :=
  ∀ (lattice : LatticeData) (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (_hHG : matrix * gramComplex lattice = 1)
    (_hGH : gramComplex lattice * matrix = 1) (_hcritical : lattice.rank = 26),
    Q lattice matrix * Q lattice matrix = 0

theorem sourceReconstruction : sourceStatement ↔ arena.Law actual := by
  constructor
  · intro source lattice matrix hHG hGH hcritical state
    change Q lattice matrix (Q lattice matrix state) = 0
    have hvalue := congrArg (fun operator : Module.End ℂ (State lattice) => operator state)
      (source lattice matrix hHG hGH hcritical)
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using hvalue
  · intro law lattice matrix hHG hGH hcritical
    apply LinearMap.ext
    intro state
    have hvalue := law lattice matrix hHG hGH hcritical state
    change Q lattice matrix (Q lattice matrix state) = 0 at hvalue
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using hvalue

theorem exactTarget : sourceStatement :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence.nilpotent

theorem actualPositive : arena.Law actual := sourceReconstruction.mp exactTarget

#print axioms sourceReconstruction
#print axioms exactTarget
#print axioms actualPositive

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence
