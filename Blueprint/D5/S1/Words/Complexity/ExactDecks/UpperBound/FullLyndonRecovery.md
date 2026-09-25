# FullLyndonRecovery

## Abstract

All bounded scattered counts are recovered unconditionally from Lyndon coordinates.

This module recovers every bounded scattered count from actual Lyndon coordinates. Its minimal-counterexample argument factors the least bad word, uses the infiltration identity to cancel shorter overlaps, and uses indexed shuffle order to isolate its positive top-degree multiplicity. The result supplies the recovery step in the exact-deck upper bound.

**Theorem 1.1 (Actual Lyndon coordinates recover every bounded count).**

$$\forall A,k,left,right, (\forall v\in\operatorname{ActualLyndonWordsThrough}\left(A, k\right),\operatorname{scatteredCount}\left(v, left\right) = \operatorname{scatteredCount}\left(v, right\right))\Rightarrow\forall w,\operatorname{length}\left(w\right)\leq k\Rightarrow\operatorname{scatteredCount}\left(w, left\right) = \operatorname{scatteredCount}\left(w, right\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/UpperBound/FullLyndonRecovery.scatteredCount_eq_of_lyndon_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A and arbitrary k,left,right, if every actual Lyndon word of length at most k has equal scattered count in left and right, then every word of length at most k has equal scattered count. No common-length premise, exact-deck premise, or guarded recovery hypothesis is required.

## References

- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/UpperBound/FullLyndonRecovery.scatteredCount_eq_of_lyndon_coordinates`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/UpperBound/IteratedOverlapBounds](IteratedOverlapBounds.md)
- Dependency: [D5/S1/Words/Complexity/ExactDecks/UpperBound/LyndonFactorization](LyndonFactorization.md)
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedShuffleOrder](../../ShuffleOrders/Indexed/IndexedShuffleOrder.md)
