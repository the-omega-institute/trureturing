import D5.S3.Observer.Separation.BooleanLowCycleBudgets
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets

open _root_.D5.S3.Observer.Separation.BooleanLowCycleBudgets
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The observed operand is the original class-wide total-budget threshold.
The law retains the original task quantifiers and all three hypotheses. -/
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
  realize signature (fun _ _ s => s + 4) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (s p q : ℕ) (_hs : s ≤ 2) (_hp : 0 < p) (_hq : 0 < q),
    UniformBudget s p q ↔ 2 ≤ p ∧ 2 ≤ q ∧ R.readout () () s ≤ p + q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb : UniformBudget 1 2 2 :=
    (h 1 2 2 (by decide) (by decide) (by decide)).mpr
      ⟨le_rfl, le_rfl, by decide⟩
  have hn := (result 1 2 2 (by decide) (by decide) (by decide)).mp hb
  omega

def registration : Registration arena
    (∀ (s p q : ℕ) (_hs : s ≤ 2) (_hp : 0 < p) (_hq : 0 < q),
      UniformBudget s p q ↔ 2 ≤ p ∧ 2 ≤ q ∧ s + 4 ≤ p + q) where
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
    exact (by decide : (0 : ℕ) + 4 ≠ 1 + 4)

register_information_theorem _root_.D5.S3.Observer.Separation.BooleanLowCycleBudgets.result
  in arena
  readout via (realize signature (fun _ _ s => s + 4) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Separation.BooleanLowCycleBudgets
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets
