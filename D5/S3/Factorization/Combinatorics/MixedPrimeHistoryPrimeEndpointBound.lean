/- GID: D5/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime endpoints and all but the last letter determine each mixed prime history of length at least two, giving an exponential counting bound. -/

import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MixedPrimeHistoryPrimeEndpointBound

open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

set_option maxHeartbeats 800000 in
/-- If m primes are at most X, at most m times (2m) to the power k minus one histories
of length k end at these primes, whenever X and k are at least two. -/
theorem prime_endpoint_count_bound (X k : ℕ) (hX : 2 ≤ X) (hk : 2 ≤ k) :
    (∑ p ∈ Nat.primesLE X, lengthCount k p) ≤
      (Nat.primesLE X).card * (2 * (Nat.primesLE X).card) ^ (k - 1) := by
  classical
  sorry

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryPrimeEndpointBound
