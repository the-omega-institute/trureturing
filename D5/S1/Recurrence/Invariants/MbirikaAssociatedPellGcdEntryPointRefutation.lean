/- GID: D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.claim; result=D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.result; claim=D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.claim
   digest: The printed associated Pell gcd-entry-point biconditional fails at k = 12. -/
/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (issue #9058)
  Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
    (statement_id sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d;
    definition Q only).
-/

import D5.S1.Recurrence.PellCompanionGcd

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.MbirikaAssociatedPellGcdEntryPointRefutation

open D5.S1.Recurrence.PellCompanionGcd (Q)

/-- Conjecture 32 as printed: for every `k ≥ 1`, `gcd(Q_k, k) > 1` iff
some prime `p` divides `k` and the entry point `e_Q(p)` — the least `r > 0`
with `p ∣ Q_r` — exists and divides `k`. -/
def claim : Prop := ∀ k : ℕ, 1 ≤ k →
  (1 < Nat.gcd (Q k) k ↔
    ∃ p : ℕ, p.Prime ∧ p ∣ k ∧ ∃ r : ℕ,
      0 < r ∧ p ∣ Q r ∧ (∀ s : ℕ, 0 < s → s < r → ¬ p ∣ Q s) ∧ r ∣ k)

example : Q 12 = 19601 := by decide
example : Nat.gcd (Q 12) 12 = 1 := by decide
example : Q 2 = 3 := by decide
example : Q 21 = 54608393 := by decide
example : Nat.gcd (Q 21) 21 = 7 := by decide

example :
    1 < Nat.gcd (Q 21) 21 ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ 21 ∧ ∃ r : ℕ,
        0 < r ∧ p ∣ Q r ∧
          (∀ s : ℕ, 0 < s → s < r → ¬ p ∣ Q s) ∧ r ∣ 21 := by
  constructor
  · decide
  · refine ⟨7, by decide, by decide, 3, by decide, by decide, ?_, by decide⟩
    intro s hs hlt
    have hs_cases : s = 1 ∨ s = 2 := by omega
    rcases hs_cases with rfl | rfl <;> decide

/-- `k = 12` refutes the printed biconditional. -/
theorem result : ¬ claim := by
  intro h
  have hiff := h 12 (by decide)
  have hrhs :
      ∃ p : ℕ, p.Prime ∧ p ∣ 12 ∧ ∃ r : ℕ,
        0 < r ∧ p ∣ Q r ∧
          (∀ s : ℕ, 0 < s → s < r → ¬ p ∣ Q s) ∧ r ∣ 12 := by
    refine ⟨3, by decide, by decide, 2, by decide, by decide, ?_, by decide⟩
    intro s hs hlt
    have hs_one : s = 1 := by omega
    subst s
    decide
  have hlhs := hiff.mpr hrhs
  exact (by decide : ¬ (1 < Nat.gcd (Q 12) 12)) hlhs

#print axioms result

end D5.S1.Recurrence.Invariants.MbirikaAssociatedPellGcdEntryPointRefutation
