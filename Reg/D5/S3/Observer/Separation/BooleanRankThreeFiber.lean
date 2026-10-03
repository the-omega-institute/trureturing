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

register_information_theorem result in arena
  readout via (realize signature (fun _ _ T => rank T) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Separation.BooleanRankThreeFiber
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
#print axioms result

end
end Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber
