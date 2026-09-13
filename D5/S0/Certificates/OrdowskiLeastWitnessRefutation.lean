/- GID: D5/S0/Certificates/OrdowskiLeastWitnessRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/OrdowskiLeastWitnessRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/OrdowskiLeastWitnessRefutation.claim; result=D5/S0/Certificates/OrdowskiLeastWitnessRefutation.result; claim=D5/S0/Certificates/OrdowskiLeastWitnessRefutation.claim
   digest: A modular certificate at n = 363 refutes Ordowski's OEIS A126762 least-witness conjecture. -/

import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.OrdowskiLeastWitnessRefutation

/-!
OEIS A126762 defines `a(n)` as the least `k > n` for which `n^k` has
remainder `n` modulo `k`. Thomas Ordowski's comment of 2018-08-03 conjectures
that the same value is the least `k > n` for which `n^(k-1)` has remainder
one modulo `k`. The claim below states that assertion directly using
`IsLeast`, avoiding an auxiliary choice of a least element.

The b-file linked in the 2021-05-25 revision gives `a(363) = 366`. Exact
kernel-checked modular arithmetic verifies the relevant entry and shows that
`363^365 % 366 = 123`, not one. The module refutes only this conjecture and
makes no claim of first discovery. The OEIS entry, revision history, b-file,
and identifier-search surfaces were checked on 2026-09-13.
-/

/-- The defining modular condition for OEIS A126762, including `k > n`. -/
def firstCongruence (n k : ℕ) : Prop :=
  n < k ∧ n ^ k % k = n % k

/-- Ordowski's proposed alternative modular condition, including `k > n`. -/
def secondCongruence (n k : ℕ) : Prop :=
  n < k ∧ n ^ (k - 1) % k = 1 % k

/-- The 2018 conjecture: the least witness for A126762 is also least for the
alternative exponent `k - 1`, for every positive input. -/
def claim : Prop :=
  ∀ n k : ℕ, 1 ≤ n →
    IsLeast {j : ℕ | firstCongruence n j} k →
    IsLeast {j : ℕ | secondCongruence n j} k

/-- At `n = 363`, the first least witness is `366`, but `366` fails the
alternative congruence because `363^365 % 366 = 123`. -/
theorem result : ¬ claim := by
  intro hclaim
  have mod_364 (t : ℕ) : 363 ^ (2 * t) % 364 = 1 := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add, Nat.mul_mod, ih]
        norm_num
  have mod_365 (t : ℕ) : 363 ^ (36 * t + 5) % 365 = 333 := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [show 36 * (t + 1) + 5 = (36 * t + 5) + 36 by omega,
          pow_add, Nat.mul_mod, ih]
        norm_num
  have mod_366_at_one (t : ℕ) : 363 ^ (5 * t + 1) % 366 = 363 := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [show 5 * (t + 1) + 1 = (5 * t + 1) + 5 by omega,
          pow_add, Nat.mul_mod, ih]
        norm_num
  have mod_366_at_zero (t : ℕ) : 363 ^ (5 * t + 5) % 366 = 123 := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [show 5 * (t + 1) + 5 = (5 * t + 5) + 5 by omega,
          pow_add, Nat.mul_mod, ih]
        norm_num
  have hfirst : IsLeast {j : ℕ | firstCongruence 363 j} 366 := by
    constructor
    · constructor
      · norm_num [firstCongruence]
      · change 363 ^ 366 % 366 = 363
        nth_rewrite 1 [show (366 : ℕ) = 5 * 73 + 1 by norm_num]
        exact mod_366_at_one 73
    · intro j hj
      by_contra hnot
      have hjlt : j < 366 := Nat.lt_of_not_ge hnot
      have hjgt : 363 < j := hj.1
      interval_cases j
      · have hbad := hj.2
        nth_rewrite 1 [show (364 : ℕ) = 2 * 182 by norm_num] at hbad
        rw [mod_364 182] at hbad
        norm_num at hbad
      · have hbad := hj.2
        nth_rewrite 1 [show (365 : ℕ) = 36 * 10 + 5 by norm_num] at hbad
        rw [mod_365 10] at hbad
        norm_num at hbad
  have hsecond := hclaim 363 366 (by norm_num) hfirst
  have hbad := hsecond.1.2
  rw [show (366 - 1 : ℕ) = 5 * 72 + 5 by norm_num,
    mod_366_at_zero 72] at hbad
  norm_num at hbad

#print axioms firstCongruence
#print axioms secondCongruence
#print axioms claim
#print axioms result

end D5.S0.Certificates.OrdowskiLeastWitnessRefutation
