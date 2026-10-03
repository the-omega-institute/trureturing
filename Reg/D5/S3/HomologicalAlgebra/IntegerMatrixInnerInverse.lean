import D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

noncomputable section
namespace Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
universe u v

abbrev Params := Σ (_ : Type u), Type v

abbrev signature : Signature where
  Params := Params.{u,v}
  State p := Matrix p.1 p.2 ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.2 ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ matrix => matrix) (fun anchor => nomatch anchor)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => fun _ _ => 1) (fun anchor => nomatch anchor)

def arena : Arena where
  signature := signature.{u,v}
  Law realization := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) (_hA : A.IsTotallyUnimodular),
      ∃ B : Matrix n m ℤ, A * B * A = realization.readout () ⟨m, n⟩ A

theorem rejected_law : ¬ arena.Law rejected.{u,v} := by
  classical
  intro law
  have hzero : (0 : Matrix (ULift.{u} Unit) (ULift.{v} Unit) ℤ).IsTotallyUnimodular := by
    intro size rows cols _ _
    cases size with
    | zero => exact ⟨1, by simp⟩
    | succ size => exact ⟨0, by simp⟩
  obtain ⟨inverse, heq⟩ := law (0 : Matrix (ULift.{u} Unit) (ULift.{v} Unit) ℤ) hzero
  have hentry := congrArg (fun matrix => matrix ⟨()⟩ ⟨()⟩) heq
  simp [rejected, realize] at hentry

theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit⟩, 0, (fun _ _ => 1), ?_⟩
  intro heq
  have hentry := congrArg (fun matrix => matrix ⟨()⟩ ⟨()⟩) heq
  change (0 : ℤ) = 1 at hentry
  exact zero_ne_one hentry

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    @_root_.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse.{u,v},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

register_information_theorem
  _root_.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse in arena
  readout via (realize signature.{u,v} (fun _ _ matrix => matrix) (fun anchor => nomatch anchor))
  realizes registration
  escape from source ({
    owner := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
