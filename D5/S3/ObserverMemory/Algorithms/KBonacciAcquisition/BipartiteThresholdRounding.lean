/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/BipartiteThresholdRounding
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/BipartiteThresholdRounding
   mirror-E: none(waiver:finite-combinatorial-lemma)
   anchors: []
   utility: none
   digest: A finite threshold pair on opposite colours has the expected product mass max(0,a+b-N). -/

import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding

open scoped BigOperators

/-! This is the finite combinatorial core of the auxiliary-threshold step in
Theorem 183.2.  The two colours use opposite half-open threshold conventions;
the statement is an exact cardinality identity and does not assume an
acquisition sampler or any probabilistic source law. -/

def crossThresholds (N a b : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun t => N - b ≤ t ∧ t < a)

/-- Opposite-colour threshold rounding realizes the positive-part product.

For `a/N` on one colour and `b/N` on the other, the admissible uniform
thresholds are exactly the interval from `N-b` up to (but excluding) `a`.
Its cardinality is the truncated integer product `a+b-N`, i.e. the finite
counterpart of `max (0, x+y-1)`. -/
theorem cross_threshold_card (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    (crossThresholds N a b).card = a + b - N := by
  classical
  have hset : crossThresholds N a b = Finset.Ico (N - b) a := by
    ext t
    simp only [crossThresholds, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico]
    constructor
    · rintro ⟨htN, hlow, hta⟩
      exact ⟨hlow, hta⟩
    · rintro ⟨hlow, hta⟩
      refine ⟨?_, hlow, hta⟩
      omega
  rw [hset, Nat.card_Ico]
  omega

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding

#print axioms D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding.cross_threshold_card
