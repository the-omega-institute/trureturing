import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{max ((max u_1 u_2) + 2) ((max (u_1 + 1) (u_2 + 1)) + 2), max ((max u_1 u_2) + 2) ((max (u_1 + 1) (u_2 + 1)) + 2), max (u_1 + 1) (u_2 + 1), 1, 1, 0, 1, 1, 0, 0, 0, max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0, 0} (@_root_.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse.{u_1, u_2}) (type_of% (arena.{u_1, u_2})) (type_of% (arena.{u_1, u_2})) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ matrix => matrix) (fun anchor => nomatch anchor))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "HomologicalAlgebra") "IntegerMatrixInnerInverse") "exists_integer_inner_inverse") "Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse/Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u_1, u_2})⟩,
  objectArena := ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ matrix => matrix) (fun anchor => nomatch anchor)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
