/- GID: D5/S3/Factorization/Combinatorics/StrictDivisorChainCount
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/StrictDivisorChainCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict divisor chains and their prime-exponent counting function. -/

import D5.S3.Factorization.Combinatorics.PrimeGenealogyCount
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Factorization.Combinatorics.StrictDivisorChainCount

/-- A chain from one to `n` with `k` strict divisibility steps, allowing arbitrary jumps. -/
def Chain (n k : ℕ) := {d : Fin (k + 1) → Fin (n + 1) //
  (d 0).val = 1 ∧ (d (Fin.last k)).val = n ∧
  ∀ i : Fin k, (d i.castSucc).val ∣ (d i.succ).val ∧ d i.castSucc < d i.succ}

/-- A chain from one to `n` whose divisibility steps may repeat an endpoint. -/
def WeakChain (n k : ℕ) := {d : Fin (k + 1) → Fin (n + 1) //
  (d 0).val = 1 ∧ (d (Fin.last k)).val = n ∧
  ∀ i : Fin k, (d i.castSucc).val ∣ (d i.succ).val ∧ d i.castSucc ≤ d i.succ}

/-- The product of the prime-exponent composition counts, with zero at length zero. -/
def weakCount (n j : ℕ) : ℕ :=
  if j = 0 then 0 else ∏ p ∈ n.primeFactors,
    (n.factorization p + j - 1).choose (n.factorization p)

/-- Strict chains form a finite type because all their endpoints are bounded. -/
instance chainFintype (n k : ℕ) : Fintype (Chain n k) :=
  inferInstanceAs (Fintype {d : Fin (k + 1) → Fin (n + 1) // _})

/-- Weak chains form a finite type because all their endpoints are bounded. -/
instance weakChainFintype (n k : ℕ) : Fintype (WeakChain n k) :=
  inferInstanceAs (Fintype {d : Fin (k + 1) → Fin (n + 1) // _})

end D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
