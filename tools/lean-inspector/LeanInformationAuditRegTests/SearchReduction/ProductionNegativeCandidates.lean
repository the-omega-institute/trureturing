import Mathlib.Data.Nat.Sqrt

/-! Actual proved inputs for production negative calibration. These are judge
fixtures, not admitted D5 results. Label certificates use only Mathlib. -/
namespace LeanInformationAudit.Tests.SearchReduction.ProductionNegativeCandidates

@[reducible] def shell : Nat → Prop → Prop
  | 0, p => p
  | k + 1, p => shell k p

theorem squareFact : (42 : Nat) * 42 = 1764 := rfl
theorem squareVia : ∃ n : Nat, n * n = 1764 := ⟨42, squareFact⟩

theorem sqrtTarget (n : Nat) : Nat.sqrt (n * n) = n := Nat.sqrt_eq n

set_option maxRecDepth 10000 in
theorem packed (n : Nat) : shell 2048 (Nat.sqrt (n * n) = n ∧ True) :=
  ⟨Nat.sqrt_eq n, True.intro⟩

set_option maxRecDepth 10000 in
theorem bounds (n : Nat) : shell 2048 (Nat.sqrt (n * n) ≤ n ∧ n ≤ Nat.sqrt (n * n)) :=
  ⟨Nat.le_of_eq (Nat.sqrt_eq n), Nat.le_of_eq (Nat.sqrt_eq n).symm⟩

set_option maxRecDepth 10000 in
theorem reverseIff (n : Nat) : shell 2048 (True ↔ Nat.sqrt (n * n) = n) :=
  ⟨fun _ => Nat.sqrt_eq n, fun _ => True.intro⟩

set_option maxRecDepth 10000 in
theorem lower (n : Nat) : shell 2048 (Nat.sqrt (n * n) ≤ n) :=
  Nat.le_of_eq (Nat.sqrt_eq n)

set_option maxRecDepth 10000 in
theorem upper (n : Nat) : shell 2048 (n ≤ Nat.sqrt (n * n)) :=
  Nat.le_of_eq (Nat.sqrt_eq n).symm

@[reducible] def wideShell : Nat → Prop → Prop
  | 0, p => p
  | k + 1, p => wideShell k True ∧ wideShell k p

theorem wideShellIntro (k : Nat) {p : Prop} (hp : p) : wideShell k p := by
  induction k generalizing p with
  | zero => exact hp
  | succ k ih => exact ⟨ih True.intro, ih hp⟩

theorem widePacked (n : Nat) : wideShell 14 (Nat.sqrt (n * n) = n ∧ True) :=
  wideShellIntro 14 ⟨Nat.sqrt_eq n, True.intro⟩

theorem hiddenTarget (n : Nat) : Nat.sqrt (n * n) = n ∧ True :=
  ⟨sqrtTarget n, True.intro⟩

theorem cachedInstance : Nat.sqrt ((10 ^ 256 + 123456789) * (10 ^ 256 + 123456789)) = (10 ^ 256 + 123456789) :=
  Nat.sqrt_eq (10 ^ 256 + 123456789)

theorem expensiveVia : Nat.sqrt ((10 ^ 256 + 123456789) * (10 ^ 256 + 123456789)) = (10 ^ 256 + 123456789) :=
  cachedInstance

end LeanInformationAudit.Tests.SearchReduction.ProductionNegativeCandidates
