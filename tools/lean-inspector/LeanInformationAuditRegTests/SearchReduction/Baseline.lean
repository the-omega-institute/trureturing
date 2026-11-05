import Mathlib.Tactic

/-! Immutable synthetic baseline for reference-search calibration. These are
judge fixtures, not research results or admitted D5 declarations. -/
namespace LeanInformationAudit.Tests.SearchReduction.Baseline

def tag (n : Nat) : Nat := 2 * n + 1

theorem tag_positive (n : Nat) : 0 < tag n := by
  unfold tag
  omega

theorem tag_odd (n : Nat) : tag n % 2 = 1 := by
  unfold tag
  omega

theorem packed (n : Nat) : 0 < tag n ∧ tag n % 2 = 1 :=
  ⟨tag_positive n, tag_odd n⟩

theorem commuted (P Q : Prop) : P ∧ Q ↔ Q ∧ P := and_comm

end LeanInformationAudit.Tests.SearchReduction.Baseline
