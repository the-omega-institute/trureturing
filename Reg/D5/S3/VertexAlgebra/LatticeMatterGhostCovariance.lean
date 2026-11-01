import Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.LatticeMatterGhostCovariance

/-! Dependent-family registration for the original-operator matter anomaly. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCovariance

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCovariance
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  T p.1 p.2.1 * (matterMode p.1 p.2.1 p.2.2 + ghostVirasoro p.1 p.2.2) -
    (matterMode p.1 p.2.1 p.2.2 + ghostVirasoro p.1 p.2.2) * T p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_ : H * gramComplex D = 1) (_ : gramComplex D * H = 1) (r : ℤ),
    R.readout () ⟨D,H,r⟩ ((-((D.rank : ℂ)/12*((r : ℂ)^3-r))) • ghostC D r)
private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 (Subsingleton.elim _ _) (Subsingleton.elim _ _) 0

def family : Registration arena (type_of% @covariance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨covariance, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    haveI := state_nontrivial zeroLattice
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@covariance) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCovariance.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCovariance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCovariance
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCovariance
