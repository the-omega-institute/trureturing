# ExactDeckCore

## Abstract

Exact fixed-length decks recover every shorter scattered count.

The exact-deck objects formalize the source paper's actual vectors of all length-k scattered-subword counts. The repository bridge first proves that, at a common source length, exact k-deck equality recovers every shorter count and is equivalent to equality of the full cutoff Magnus vector.

**Definition 1.1 (An actual exact k-deck).**

$$exactKDeck$$

*Formalization.* `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.exactKDeck` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, exactKDeck k source is the function sending each actual pattern of length exactly k to its scatteredCount in source.

**Definition 1.2 (Decks realized at one source length).**

$$exactKDeckImage$$

*Formalization.* `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.exactKDeckImage` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

exactKDeckImage A k n is the finite image of exactKDeck k on all actual words over A of length exactly n.

**Theorem 1.3 (Exact decks recover all shorter counts).**

$$scatteredCounteqofexactKDeckeq$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.scatteredCount_eq_of_exactKDeck_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A with decidable equality, common length n, k<=n, and a pattern of length at most k, equality of exactKDeck k for the two source words implies equality of that pattern's scattered counts.

**Theorem 1.4 (Exact-deck and cutoff equality coincide).**

$$exactKDeckeqiffcutoffMagnuseqofcommonlength$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, source words of the same length n, and k<=n, equality of their actual exact k-decks is equivalent to equality of cutoffMagnus k.

## References

- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.exactKDeck`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.exactKDeckImage`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.scatteredCount_eq_of_exactKDeck_eq`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth](PositivePairBallGrowth.md)
