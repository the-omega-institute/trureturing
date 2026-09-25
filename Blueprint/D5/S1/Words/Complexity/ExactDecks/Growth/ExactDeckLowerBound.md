# ExactDeckLowerBound

## Abstract

Fixed-length padding loses exactly one degree in the exact-deck lower bound.

The exact-deck objects formalize the source paper's actual vectors of all length-k scattered-subword counts. The repository bridge first proves that, at a common source length, exact k-deck equality recovers every shorter count and is equivalent to equality of the full cutoff Magnus vector.

**Theorem 1.1 (Weighted-Lyndon lower growth for exact decks).**

$$actualexactKDeckImageweightedLyndonlowerbound$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckLowerBound.actual_exactKDeckImage_weightedLyndon_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite linearly ordered A with at least two letters and every k>=1, there are naturals C,N with 0<C such that for all n>=N, n^(weightedLyndonExponent A k-1) <= C*(exactKDeckImage A k n).card. Padding turns a ball representative into a word of exact length n while retaining an injective deck encoding.

## References

- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckLowerBound.actual_exactKDeckImage_weightedLyndon_lower_bound`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore](ExactDeckCore.md)
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth](PositivePairBallGrowth.md)
