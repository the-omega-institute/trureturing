/- GID: D5/S1/Deficit/LambdaMinusAdditive
   generality: I
   mirror-B: D5/B/S1/Deficit/LambdaMinusAdditive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The contraction-face reading lambdaMinus is additive over coprime factors: lambdaMinus (m*n) = lambdaMinus m + lambdaMinus n whenever m, n are coprime, since their prime supports are disjoint. -/

import D5.S1.Deficit.AlmostAdditivity
import Mathlib

namespace D5.S1.Deficit.LambdaMinusAdditive

open D5.S1.Deficit
open D5.S1.Deficit.AlmostAdditivity

/-- The contraction-face reading `lambdaMinus` is additive over coprime factors:
`lambdaMinus (m * n) = lambdaMinus m + lambdaMinus n` for coprime `m, n`.
This is the exact companion of `lambdaMinus_almost_additive`: on coprimes the common-factor
error term vanishes because the prime supports are disjoint. -/
theorem lambdaMinus_coprime_add {m n : ℕ} (h : Nat.Coprime m n) :
    lambdaMinus (m * n) = lambdaMinus m + lambdaMinus n := by
  classical
  have hdis : Disjoint m.factorization.support n.factorization.support := by
    rw [Nat.support_factorization, Nat.support_factorization]
    exact Nat.Coprime.disjoint_primeFactors h
  rw [lambdaMinus, lambdaMinus, lambdaMinus, Nat.factorization_mul_of_coprime h]
  exact Finsupp.sum_add_index_of_disjoint hdis _

end D5.S1.Deficit.LambdaMinusAdditive
