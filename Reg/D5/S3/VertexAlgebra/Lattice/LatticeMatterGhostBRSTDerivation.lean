import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation

open scoped VertexOperator
open _root_.D5.S3.VertexAlgebra
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation

/- The readout is the actual operator equality as a predicate of its right
operand. The law keeps the entire original homogeneous-state telescope. -/
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ,
    State D × ℕ × ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (p : signature.Params) : signature.State p :=
  LatticeBRST.totalCharge p.1 p.2.1 *
      ((LatticeMatterGhostStateField.Y p.1 p.2.2.1)[[p.2.2.2.2]]) -
    (-1 : ℂ)^p.2.2.2.1 •
      (((LatticeMatterGhostStateField.Y p.1 p.2.2.1)[[p.2.2.2.2]]) *
        LatticeBRST.totalCharge p.1 p.2.1)

def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (s : State D) (p : ℕ)
    (_ : LatticeMatterGhostStateField.parity D s = (-1 : ℂ)^p • s) (n : ℤ),
    R.readout () ⟨D,H,s,p,n⟩
      ((LatticeMatterGhostStateField.Y D (LatticeBRST.totalCharge D H s))[[n]])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0 0 (by simp) 0

def family : Registration arena (type_of% @totalCharge_field_superderivation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨totalCharge_field_superderivation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : signature.Params := ⟨zeroLattice,0,0,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@totalCharge_field_superderivation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => lhs p = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation
