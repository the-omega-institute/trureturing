/- GID: D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/StephanFloorSqrtRecurrenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.claim; result=D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.result; claim=D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.claim
   digest: The n = 17 term refutes Stephan's conjectured recurrence for OEIS A104863. -/

import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.StephanFloorSqrtRecurrenceRefutation

/-!
OEIS A104863 defines the sequence by the floor square-root recurrence with
initial values 10 and 30.  The sentinel value at index zero makes the
definition total; every index used by the conjecture is at least 17.

Ralf Stephan's OEIS formula conjectures that, for every `n ≥ 17`, the term
at `n` equals the terms at `n - 2` and `n - 4` plus one.  At `n = 17`, the
recurrence gives 935, while the proposed right-hand side is 578 + 358 + 1.
-/

/-- The OEIS A104863 sequence, with a zero sentinel at index zero. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 10
  | 2 => 30
  | n + 3 => Nat.sqrt (a (n + 2) ^ 2 + a (n + 1) ^ 2)

/-- Stephan's conjectured recurrence, stated for all indices in its domain. -/
def claim : Prop :=
  ∀ n : ℕ, 17 ≤ n → a n = a (n - 2) + a (n - 4) + 1

/-- The conjectured recurrence fails at its first stated index, `n = 17`. -/
theorem result : ¬ claim := by
  have h3 : a 3 = 31 := by
    change Nat.sqrt (30 ^ 2 + 10 ^ 2) = 31
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h4 : a 4 = 43 := by
    change Nat.sqrt (a 3 ^ 2 + a 2 ^ 2) = 43
    rw [h3]
    exact (Nat.eq_sqrt'.2 (by norm_num [a])).symm
  have h5 : a 5 = 53 := by
    change Nat.sqrt (a 4 ^ 2 + a 3 ^ 2) = 53
    rw [h4, h3]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h6 : a 6 = 68 := by
    change Nat.sqrt (a 5 ^ 2 + a 4 ^ 2) = 68
    rw [h5, h4]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h7 : a 7 = 86 := by
    change Nat.sqrt (a 6 ^ 2 + a 5 ^ 2) = 86
    rw [h6, h5]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h8 : a 8 = 109 := by
    change Nat.sqrt (a 7 ^ 2 + a 6 ^ 2) = 109
    rw [h7, h6]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h9 : a 9 = 138 := by
    change Nat.sqrt (a 8 ^ 2 + a 7 ^ 2) = 138
    rw [h8, h7]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h10 : a 10 = 175 := by
    change Nat.sqrt (a 9 ^ 2 + a 8 ^ 2) = 175
    rw [h9, h8]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h11 : a 11 = 222 := by
    change Nat.sqrt (a 10 ^ 2 + a 9 ^ 2) = 222
    rw [h10, h9]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h12 : a 12 = 282 := by
    change Nat.sqrt (a 11 ^ 2 + a 10 ^ 2) = 282
    rw [h11, h10]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h13 : a 13 = 358 := by
    change Nat.sqrt (a 12 ^ 2 + a 11 ^ 2) = 358
    rw [h12, h11]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h14 : a 14 = 455 := by
    change Nat.sqrt (a 13 ^ 2 + a 12 ^ 2) = 455
    rw [h13, h12]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h15 : a 15 = 578 := by
    change Nat.sqrt (a 14 ^ 2 + a 13 ^ 2) = 578
    rw [h14, h13]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h16 : a 16 = 735 := by
    change Nat.sqrt (a 15 ^ 2 + a 14 ^ 2) = 735
    rw [h15, h14]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  have h17 : a 17 = 935 := by
    change Nat.sqrt (a 16 ^ 2 + a 15 ^ 2) = 935
    rw [h16, h15]
    exact (Nat.eq_sqrt'.2 (by norm_num)).symm
  intro hclaim
  have hrec := hclaim 17 (by decide)
  rw [h17, h15, h13] at hrec
  norm_num at hrec

#print axioms a
#print axioms claim
#print axioms result

end D5.S0.Certificates.StephanFloorSqrtRecurrenceRefutation
