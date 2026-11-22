# Whole-permutation diagonal hits from fixed marked prefixes

## Abstract

An actual fixed-prefix hit transfers to the whole original finite permutation.

**Definition 1.1 (Actual finite literal hit probability).**

$$\operatorname{P}\left(e, n\right)=\operatorname{actualMass}\left(n, \operatorname{hitsDiagonal}\left(e\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit.literalHitProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P(e,n) is the actual uniform mass of length-n avoiding permutations having at least one original-coordinate point whose position minus value is the fixed integer e. The event is inspected on the original permutation, not on a parsed cycle.

**Theorem 1.2 (Fixed-prefix lower bounds and conditional probability-one limit).**

$$\begin{gathered}(\forall k,a, a<\operatorname{firstKHitProbability}\left(k, e\right)\longrightarrow \operatorname{Eventually}\left(n\mapsto a<\operatorname{P}\left(e, n\right)\right)) \land\\{}(\operatorname{StreamHitsAlmostSurely}\left(e\right)\longrightarrow \lim_{n\to\infty}\operatorname{P}\left(e, n\right)=1)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit.finite_avoider_literal_hit_limit_of_stream_hit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed e and every natural prefix length k, the first conjunct gives an eventual strict lower bound at each real a below the stream's first-k probability. The second assumes that almost every stream eventually has a marked-cycle hit at e plus the preceding discrepancy; it does not prove that premise.

A successful finite-prefix hit already exhibits an original coordinate witnessing the whole-permutation event, and uniform outer mass is monotone. The first-k stream events increase to the event of any marked hit. Given a tolerance, first choose a single k from the stream law; only then send n to infinity using the fixed-prefix limit. The full mass is at most one. There is no growing offset, joint k,n limit, rate, or multiplicity claim.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit.finite_avoider_literal_hit_limit_of_stream_hit`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit.literalHitProbability`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit](EndpointFirstCycleHitLimit.md)
