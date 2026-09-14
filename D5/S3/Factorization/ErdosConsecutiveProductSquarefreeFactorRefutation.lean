/- GID: D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
   generality: I
   mirror-B: D5/B/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.NumberTheory.Primorial, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim; result=D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.result; claim=D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim
   digest: The starting value 47 refutes uniqueness of Erdos's 23 in the consecutive-product question. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.ErdosConsecutiveProductSquarefreeFactorRefutation

/-- The product of the `k` integers immediately following `x`. -/
def P (x k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (x + i)

/-- The product of prime factors of `P x k` having exponent exactly one. -/
def v (x k : ℕ) : ℕ :=
  ∏ p ∈ (P x k).primeFactors.filter (fun p => (P x k).factorization p = 1), p

/-- The complementary product of prime powers having exponent at least two. -/
def u (x k : ℕ) : ℕ :=
  ∏ p ∈ (P x k).primeFactors.filter (fun p => 2 ≤ (P x k).factorization p),
    p ^ (P x k).factorization p

/-- The reported suggestion that 23 is the sole positive exceptional starting value. -/
def claim : Prop :=
  ∀ x : ℕ, 1 ≤ x → x ≠ 23 → ∃ k : ℕ, 1 ≤ k ∧ u x k < v x k

private theorem finite_cases (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 1) :
    v 47 k < u 47 k := by
  have hf : (P 47 k).factorization =
      ∑ i ∈ Finset.Icc 1 k, (47 + i).factorization := by
    unfold P
    apply Nat.factorization_prod
    intro i _
    omega
  have hs (S : Finset ℕ) :
      (∑ i ∈ S, (47 + i).factorization).support =
        S.biUnion (fun i => (47 + i).primeFactors) := by
    induction S using Finset.induction with
    | empty => simp
    | @insert i S hi ih =>
        simp only [Finset.sum_insert hi, Finset.biUnion_insert, Finsupp.support_add_eq_union,
          Nat.support_factorization, ih]
  simp only [v, u, ← Nat.support_factorization, hf, hs]
  interval_cases k <;> decide +kernel

end D5.S3.Factorization.ErdosConsecutiveProductSquarefreeFactorRefutation
