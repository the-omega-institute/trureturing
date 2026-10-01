import D5.S3.Observer.Separation.BooleanRankFour
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.BooleanRankFour

open _root_.D5.S3.Observer.Separation.BooleanRankFour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The entire source conjunction; only the left budget's selected occurrence varies. -/
def arena : Arena where
  signature := signature
  Law R :=
    ActiveConnected F4 ∧ cycleRank F4 = 4 ∧
    (leftConflict F4).chromaticNumber = 2 ∧
    (rightConflict F4).chromaticNumber = 2 ∧
    (∀ p q, Admits F4 (R.readout () () p) q ↔ Region p q) ∧
    (∀ s : ℤ, 4 ≤ s → ∀ p q, Uniform s p q ↔ Region p q)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have admits : Admits F4 0 4 := (h.2.2.2.2.1 2 4).mpr (by norm_num [Region])
  have region : Region 0 4 := (result.2.2.2.2.1 0 4).mp admits
  norm_num [Region] at region

def registration : Registration arena
    (ActiveConnected F4 ∧ cycleRank F4 = 4 ∧
    (leftConflict F4).chromaticNumber = 2 ∧
    (rightConflict F4).chromaticNumber = 2 ∧
    (∀ p q, Admits F4 p q ↔ Region p q) ∧
    (∀ s : ℤ, 4 ≤ s → ∀ p q, Uniform s p q ↔ Region p q)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (0 : ℕ) ≠ 1
    decide

register_information_theorem result in arena
  readout via (realize signature (fun _ _ p => p) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Separation.BooleanRankFour
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "fn", "arg", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Observer.Separation.BooleanRankFour
