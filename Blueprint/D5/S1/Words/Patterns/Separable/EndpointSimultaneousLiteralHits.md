# Simultaneous diagonal hits in finite separable permutations

## Abstract

Every fixed finite collection of original-coordinate diagonals is hit with asymptotic probability one.

**Definition 1.1 (Actual probability of hitting every specified diagonal).**

$$\operatorname{P}\left(S, n\right)=\operatorname{actualMass}\left(n, p\mapsto \forall e\in S, \operatorname{hitsDiagonal}\left(p, e\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits.simultaneousLiteralHitProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same uniform length-n avoiding permutation is tested against every e in S. The event tests position minus value in the original coordinates. For the empty set the test is vacuous.

**Theorem 1.2 (Probability-one limit for every fixed finite offset set).**

$$\forall S, \lim_{n\to\infty}\operatorname{P}\left(S, n\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits.simultaneous_literal_hits_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set S is a fixed finite subset of the integers, chosen independently of n. Taking S to be a singleton recovers the limit for one fixed diagonal, and the singleton zero gives the existence of a fixed point with probability tending to one.

Almost-sure recurrence in the actual marked stream supplies an eventual hit at each fixed offset. The fixed-prefix transfer gives a finite-permutation probability-one limit separately for each offset. Failure to hit all specified diagonals is a finite union of failures; its probability is bounded by the finite sum of the individual failure probabilities, which tends to zero. No independence of diagonal events is assumed.

The result gives neither a rate nor a limit for sets varying with n. It does not claim multiple points on any single diagonal.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits.simultaneousLiteralHitProbability`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits.simultaneous_literal_hits_limit`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointCycleHazardAccumulation](EndpointCycleHazardAccumulation.md)
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit](EndpointFiniteLiteralHit.md)
