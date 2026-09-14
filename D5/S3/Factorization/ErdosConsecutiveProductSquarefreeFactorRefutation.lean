/- GID: D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
   generality: I
   mirror-B: D5/B/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.NumberTheory.Primorial]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim; result=D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.result; claim=D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim
   digest: The starting value 47 refutes uniqueness of Erdos's 23 in the consecutive-product question. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Primorial

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

private theorem first_case : v 47 1 < u 47 1 := by
  decide +kernel

end D5.S3.Factorization.ErdosConsecutiveProductSquarefreeFactorRefutation
