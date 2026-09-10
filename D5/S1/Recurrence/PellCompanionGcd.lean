/- GID: D5/S1/Recurrence/PellCompanionGcd
   generality: I
   mirror-B: D5/B/S1/Recurrence/PellCompanionGcd
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pell and companion Pell coprimality proves the A084068 gcd formula. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace D5.S1.Recurrence.PellCompanionGcd

/- The proposed escape witness is pell_companion_step: the first-order cross
   recurrence is derived from the two second-order recurrences by induction.
   The main gcd formula is a bind-only companion using the coprimality and
   parity results below. Admission basis: escape-witness. All declarations
   concern arbitrary indices; utility none (no finite computation delivered).
   Consumer -> prerequisite: pell_companion_gcd -> pell_companion_coprime,
   companion_odd; pell_companion_coprime, companion_odd -> pell_companion_step.
   No direct frozen D5 dependencies. -/

/-- Pell numbers, with initial values zero and one. -/
def P : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * P (n + 1) + P n

/-- Companion Pell numbers, with both initial values equal to one. -/
def Q : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * Q (n + 1) + Q n

/-- The two second-order sequences satisfy a coupled first-order recurrence. -/
theorem pell_companion_step (n : Nat) :
    P (n + 1) = P n + Q n ∧ Q (n + 1) = 2 * P n + Q n := by
  induction n with
  | zero => simp [P, Q]
  | succ n ih =>
      change P (n + 2) = P (n + 1) + Q (n + 1) ∧
        Q (n + 2) = 2 * P (n + 1) + Q (n + 1)
      rw [P, Q]
      omega

/-- Pell and companion Pell numbers at the same index are coprime. -/
theorem pell_companion_coprime (n : Nat) : Nat.Coprime (P n) (Q n) := by
  induction n with
  | zero => simp [P, Q]
  | succ n ih =>
      rw [(pell_companion_step n).1, (pell_companion_step n).2]
      rw [show 2 * P n + Q n = P n + (P n + Q n) by omega]
      rw [Nat.coprime_add_self_right, Nat.coprime_self_add_left]
      exact ih.symm

/-- Every companion Pell number is odd, including the initial value. -/
theorem companion_odd (n : Nat) : Odd (Q n) := by
  induction n with
  | zero => simp [Q]
  | succ n ih =>
      rw [(pell_companion_step n).2]
      obtain ⟨k, hk⟩ := ih
      exact ⟨P n + k, by omega⟩

/-- The normalized gcd conjecture from OEIS A084068, also valid at index zero. -/
theorem pell_companion_gcd (n : Nat) :
    Nat.gcd (if 2 ∣ n then 2 * P n ^ 2 else Q n ^ 2) (P n * Q n) =
      (if 2 ∣ n then P n else Q n) := by
  have hc := pell_companion_coprime n
  split_ifs with hn
  · have hc2 : Nat.Coprime (2 * P n) (Q n) :=
      (companion_odd n).coprime_two_left.mul_left hc
    calc
      Nat.gcd (2 * P n ^ 2) (P n * Q n) =
          Nat.gcd (P n * (2 * P n)) (P n * Q n) := by congr 1; ring
      _ = P n * Nat.gcd (2 * P n) (Q n) := Nat.gcd_mul_left ..
      _ = P n := by rw [hc2.gcd_eq_one, Nat.mul_one]
  · calc
      Nat.gcd (Q n ^ 2) (P n * Q n) =
          Nat.gcd (Q n * Q n) (Q n * P n) := by rw [pow_two, Nat.mul_comm (P n)]
      _ = Q n * Nat.gcd (Q n) (P n) := Nat.gcd_mul_left ..
      _ = Q n := by rw [hc.symm.gcd_eq_one, Nat.mul_one]

#print axioms pell_companion_step
#print axioms pell_companion_coprime
#print axioms companion_odd
#print axioms pell_companion_gcd

end D5.S1.Recurrence.PellCompanionGcd
