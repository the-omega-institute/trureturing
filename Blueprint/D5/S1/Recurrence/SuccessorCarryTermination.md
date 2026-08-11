# Zeckendorf Successor Carry Termination

## Abstract

Zeckendorf successor carry positions are bounded by the highest Fibonacci index.

**Theorem 1.1 (The successor carry chain terminates within the highest index).**

$$\forall n\in\mathbb{N},\ \operatorname{card}(Carry(n)) \leq \operatorname{greatestFib}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SuccessorCarryTermination.successor_carry_chain_terminates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increment a natural number and compare its two canonical Zeckendorf representations. The successor carry positions are exactly the occupied Fibonacci indices present before the increment and absent afterward. Their number is bounded by the greatest Fibonacci index of the original number, so propagation cannot continue beyond the highest occupied scale. A companion theorem checks that the Fibonacci weight removed by these positions, plus one, equals the weight introduced by normalization; this makes the finite trace an arithmetic carry certificate rather than only a set-theoretic difference.

The pinned library was searched before proving. It provides the canonical Zeckendorf representation, exact decoding by Fibonacci summation, its successor unfolding, and the two-index descent of each greedy tail. It has no declaration bounding a successor carry trace or even the length of a canonical representation by its greatest Fibonacci index. The deposited proof derives that length bound by strong induction through the library's tail descent and then transfers it to the carry-position subset. This is a new proof over library primitives, not a thin wrapper and not a duplicate of the general local normalizer already present in the repository.

## References

- Truth anchor: `D5/S1/Recurrence/SuccessorCarryTermination.successor_carry_chain_terminates`
