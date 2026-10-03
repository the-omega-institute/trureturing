/- GID: D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.claim; result=D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result; claim=D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.claim
   digest: The formula is negative at (26,11,1). -/

/-
proof_shape: result: bind-only (finite binomial computation and natural-cast nonnegativity).
escape_witness: none
admission_basis: open-problem-resolution (#12305; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial

open scoped BigOperators

namespace D5.S0.Certificates.Combinatorics.RationalQSystemInfinityCountRefutation

/-- The integer expression on the right of Hou--Jiang--Miao (C.2). -/
def formula (L M n : ℕ) : ℤ :=
  (L.choose (M - n) : ℤ) - ∑ x ∈ Finset.range (M - n), (L.choose x : ℤ)

/-- The even-length, no-twist infinite-root scope at η = iπ/3. -/
def Admissible (L M n : ℕ) : Prop :=
  Even L ∧ 1 ≤ M ∧ 2 * M ≤ L ∧ 1 ≤ n ∧ n ≤ 2 ∧ n ≤ M ∧
    (L : ℤ) ≡ 2 * ((M : ℤ) - n) [ZMOD 6]

/-- A necessary consequence of (C.2): its values are natural-number counts. -/
def claim : Prop :=
  ∃ N : ℕ → ℕ → ℕ → ℕ, ∀ L M n, Admissible L M n →
    (N L M n : ℤ) = formula L M n

example : Admissible 26 11 1 := by
  unfold Admissible
  refine ⟨⟨13, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_⟩
  norm_num [Int.ModEq]

example : Nonempty (ℕ → ℕ → ℕ → ℕ) :=
  ⟨fun _ _ _ => 0⟩

/-- The admissible triple (26,11,1) makes (C.2) negative. -/
theorem result : ¬ claim := by
  rintro ⟨N, hN⟩
  have hAdmissible : Admissible 26 11 1 := by
    unfold Admissible
    refine ⟨⟨13, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_⟩
    norm_num [Int.ModEq]
  have hValue : formula 26 11 1 = -346802 := by
    norm_num [formula, Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial]
  have hNonnegative : (0 : ℤ) ≤ (N 26 11 1 : ℤ) := Int.natCast_nonneg _
  rw [hN 26 11 1 hAdmissible, hValue] at hNonnegative
  norm_num at hNonnegative

end D5.S0.Certificates.Combinatorics.RationalQSystemInfinityCountRefutation
