import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyNonvacuity

/-! Full original telescope and actual coefficient readout. This is an
unfinished source-occurrence binding attempt, never a validated certificate.
Other public helpers in this source module are not claimed registered. -/
open scoped VertexOperator
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (State)
open _root_.D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyNonvacuity

abbrev signature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ × State D
  State x := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (x : signature.Params) : signature.State x :=
  vacuumCoeff x.1 (LatticeBRST.totalCharge x.1 x.2.1 x.2.2)

def actual : Realization signature := realize signature
  (fun _ x y => lhs x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : State D),
    R.readout () ⟨D,H,a⟩ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0

def family : Registration arena (type_of% @vacuumCoeff_charge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨vacuumCoeff_charge, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let x : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@vacuumCoeff_charge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyNonvacuity.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyNonvacuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => lhs x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeBRSTCohomologyNonvacuity
