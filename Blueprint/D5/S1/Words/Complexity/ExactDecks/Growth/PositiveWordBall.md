# PositiveWordBall

## Abstract

Actual central digits inject the preceding cutoff ball into the next degree.

The exponent uses the cardinalities of actual Lyndon-word subtypes at every degree. The proof combines a complete degree-one letter box with the multi-scale central digits at higher degrees, always using images of actual positive words rather than an abstract free-coordinate family.

**Definition 1.1 (The actual cutoff-Magnus ball).**

$$positiveWordBall$$

*Formalization.* `D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall.positiveWordBall` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, positiveWordBall A r n is the finite image of cutoffMagnus r on all actual lists over A whose length is at most n.

**Definition 1.2 (Weighted actual Lyndon exponent).**

$$weightedLyndonExponent$$

*Formalization.* `D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall.weightedLyndonExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A, weightedLyndonExponent A r is sum over i in range(r+1) of i*actualLyndonCount A i; the degree-zero term is present syntactically and vanishes.

**Theorem 1.3 (One central-digit growth step).**

$$positiveWordBallcardstep$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall.positiveWordBall_card_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For degree r>=2, if a radius n accommodates a radius-m representative from degree r-1 followed by the complete degree-r, t-scale central digit word, then the degree-r positive-word ball has at least the product of the preceding ball cardinality and (2^r)^(t*actualLyndonCount A r).

## References

- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall.positiveWordBall`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall.positiveWordBall_card_step`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall.weightedLyndonExponent`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection](../../PositivePairs/Digits/CentralDigitInjection.md)
