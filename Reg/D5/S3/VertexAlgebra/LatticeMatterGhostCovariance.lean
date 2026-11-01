import Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.LatticeMatterGhostCovariance

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCovariance

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCovariance
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

abbrev arena : Arena where
  signature := Equality.signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_ : H * gramComplex D = 1) (_ : gramComplex D * H = 1) (r : ℤ),
    R.readout () ⟨Module.End ℂ (State D),
      T D H * (matterMode D H r + ghostVirasoro D r) -
        (matterMode D H r + ghostVirasoro D r) * T D H⟩
      ((-((D.rank : ℂ)/12*((r : ℂ)^3-r))) • ghostC D r)
private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp
private theorem rejected_law : ¬ arena.Law Equality.rejected := by
  intro h
  exact h zeroLattice 0 (Subsingleton.elim _ _) (Subsingleton.elim _ _) 0

def family : Registration arena (type_of% @covariance) where
  actual := Equality.actual
  bridge := Iff.rfl
  variation := ⟨covariance, Equality.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Equality.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Equality.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@covariance) (Realization Equality.signature) Unit Unit where
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
  readout := some (realize Equality.signature Equality.actual.readout Equality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostCovariance
    definition := none
    coordinates := #[]
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
