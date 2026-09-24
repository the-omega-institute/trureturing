# Exact k-Deck Asymptotics

## Abstract

For every finite ordered alphabet of size at least two and every positive k, actual exact k-deck images have the full weighted-Lyndon Theta exponent.

The lower estimate comes from actual equal-length positive-word constructions. For the upper estimate, one singleton Lyndon coordinate is erased and recovered from the fixed total source length; unconditional Lyndon-coordinate recovery then identifies the complete exact deck. Thus exactly one degree of freedom is removed, without an additional hypothesis on n or k.

**Theorem 1.1 (Full exact k-deck Conjecture 8.1 asymptotics).**

$$actualexactKDeckImageweightedLyndonisTheta$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairExactDeckAsymptotics.actual_exactKDeckImage_weightedLyndon_isTheta` (`✓ std3`). ∎

*Resolves.* `Problems/nilforoushan-parvaresh-conjecture-8-1` (proved) by `D5/S1/Words/Complexity/PositivePairExactDeckAsymptotics.actual_exactKDeckImage_weightedLyndon_isTheta`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nilforoushan-parvaresh-conjecture-8-1","declaration_gid":"D5/S1/Words/Complexity/PositivePairExactDeckAsymptotics.actual_exactKDeckImage_weightedLyndon_isTheta","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite linearly ordered type A with 2<=Fintype.card A, every k:N with 1<=k, the real-valued function n |-> (exactKDeckImage A k n).card is Real.IsTheta at Filter.atTop of n |-> (n:R)^(weightedLyndonExponent A k-1). Here weightedLyndonExponent is the weighted sum of the actual length-r Lyndon-word counts, so the theorem has all source quantifiers and no proxy parameter.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairExactDeckAsymptotics.actual_exactKDeckImage_weightedLyndon_isTheta`
- Dependency: [D5/S1/Words/Complexity/PositivePairExactDeckUpperBound](PositivePairExactDeckUpperBound.md)
