import Lean
import Lean.Elab.Tactic.Omega

namespace LeanInformationAudit.Tests.SearchReduction.GraphCandidates

theorem scopedApply (p q : Prop) (f : p → q) (h : p) : q := f h

private theorem parametricHelper (x : Nat) : x = x := rfl

theorem helperApplications (a b : Nat) : a = a ∧ b = b :=
  ⟨parametricHelper a, parametricHelper b⟩

theorem squareFact : (42 : Nat) * 42 = 1764 := rfl

theorem trueFact : True := True.intro

theorem arithmeticFact : (1 : Nat) + 1 = 2 := rfl

theorem squareVia : ∃ n : Nat, n * n = 1764 := ⟨42, squareFact⟩

theorem secondSquareFact : (43 : Nat) * 43 = 1849 := rfl

theorem secondWitness : ∃ m : Nat, m * m = 1849 := ⟨43, secondSquareFact⟩

theorem twoLayerVia : ∃ n : Nat, n * n = 1764 ∧ ∃ m : Nat, m * m = 1849 :=
  ⟨42, squareFact, secondWitness⟩

theorem sharedRoutine : ∃ n : Nat, n = 0 ∧ n = 0 := ⟨0, rfl, rfl⟩

theorem successorFact : (42 : Nat) + 1 = 43 := rfl

theorem sharedWitness : ∃ n : Nat, n * n = 1764 ∧ n + 1 = 43 :=
  ⟨42, squareFact, successorFact⟩

theorem routineHelper (n : Nat) : n < n + 1 := by omega

theorem routineVia (n : Nat) : n < n + 1 := routineHelper n

theorem square : ∃ n : Nat, n * n = 1764 := ⟨42, rfl⟩

theorem scopedWitness (x : Nat) (hx : x * x = 1764) : ∃ n : Nat, n * n = 1764 := ⟨x, hx⟩

theorem nested : ∃ n : Nat, n * n = 1764 ∧ ∃ m : Nat, m * m = 1849 :=
  ⟨42, rfl, 43, rfl⟩

private theorem squareHelper : ∃ n : Nat, n * n = 1764 := ⟨42, rfl⟩

theorem splitHelper : ∃ n : Nat, n * n = 1764 := squareHelper

theorem dead : ∃ n : Nat, n * n = 1764 := by
  have unused : (123 : Nat) = 123 := rfl
  exact ⟨42, rfl⟩

end LeanInformationAudit.Tests.SearchReduction.GraphCandidates
