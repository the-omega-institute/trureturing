import Lean

namespace LeanInformationAudit.Tests.SearchReduction.GraphCandidates

theorem squareFact : (42 : Nat) * 42 = 1764 := rfl

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
