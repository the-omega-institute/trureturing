# Growth of Actual Positive-Word Balls

## Abstract

Actual positive words realize the full weighted-Lyndon polynomial lower growth of every positive cutoff-Magnus ball.

The exponent uses the cardinalities of actual Lyndon-word subtypes at every degree. The proof combines a complete degree-one letter box with the multi-scale central digits at higher degrees, always using images of actual positive words rather than an abstract free-coordinate family.

**Definition 1.1 (The actual cutoff-Magnus ball).**

$$positiveWordBall$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairBallGrowth.positiveWordBall` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite A, positiveWordBall A r n is the finite image of cutoffMagnus r on all actual lists over A whose length is at most n.

**Definition 1.2 (Weighted actual Lyndon exponent).**

$$weightedLyndonExponent$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairBallGrowth.weightedLyndonExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A, weightedLyndonExponent A r is sum over i in range(r+1) of i*actualLyndonCount A i; the degree-zero term is present syntactically and vanishes.

**Theorem 1.3 (All-radius weighted-Lyndon lower growth).**

$$actualpositiveWordBallweightedLyndonlowerbound$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairBallGrowth.actual_positiveWordBall_weightedLyndon_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite linearly ordered A with 2<=Fintype.card A and every r with 1<=r, there are naturals C,N with 0<C such that for every n>=N, n^(weightedLyndonExponent A r) <= C*(positiveWordBall A r n).card.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairBallGrowth.actual_positiveWordBall_weightedLyndon_lower_bound`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairBallGrowth.positiveWordBall`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairBallGrowth.weightedLyndonExponent`
- Dependency: [D5/S1/Words/Complexity/PositivePairCentralDigits](PositivePairCentralDigits.md)
