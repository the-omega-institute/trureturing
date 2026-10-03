import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.BooleanRankThreeFiber
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber
open _root_.D5.S3.Observer.Separation.BooleanRankThreeFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Task (Fin 8) (Fin 6)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => rank T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (T : Task X Y), Admissible T →
      ((∃ c d, Balanced T (residual T c d)) → HasBudget T 3 3) ∧
      ((∀ c d, ¬ Balanced T (residual T c d)) →
        3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T)) ∧
      (¬ HasBudget T 3 3 → 3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T))) ∧
    (∃ T : Task (Fin 8) (Fin 6), Admissible T ∧ R.readout () () T = 3 ∧
      (∀ c d, ¬ Balanced T (residual T c d)) ∧ RankThreeShape T ∧ HasBudget T 3 3)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, T, _, h, _⟩
  change (0 : ℤ) = 3 at h
  norm_num at h

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), ⟨fun _ _ => none⟩, ⟨fun _ _ => some 0⟩, ?_⟩
    change rank (Task.mk (fun (_ : Fin 8) (_ : Fin 6) => none)) ≠
      rank (Task.mk (fun (_ : Fin 8) (_ : Fin 6) => some 0))
    simp only [rank, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide +kernel

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Observer.Separation.BooleanRankThreeFiber.result) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ T => rank T) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Separation") "BooleanRankThreeFiber") "result") "Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber/Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ T => rank T) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Separation.BooleanRankThreeFiber, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
#print axioms result

end
end Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber
