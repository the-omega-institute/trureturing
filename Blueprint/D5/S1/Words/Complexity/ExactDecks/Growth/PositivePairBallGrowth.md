# PositivePairBallGrowth

## Abstract

Actual positive-word cutoff balls have weighted Lyndon polynomial growth.

The exponent uses the cardinalities of actual Lyndon-word subtypes at every degree. The proof combines a complete degree-one letter box with the multi-scale central digits at higher degrees, always using images of actual positive words rather than an abstract free-coordinate family.

**Theorem 1.1 (All-radius weighted-Lyndon lower growth).**

$$\forall A, r, \operatorname{card}\left(A\right)\geq2\land r\geq1\Rightarrow\exists C,N, 0< C\land\forall n\geq N, \operatorname{pow}\left(n, \operatorname{weightedLyndonExponent}\left(A, r\right)\right)\leq C \cdot \operatorname{card}\left(\operatorname{positiveWordBall}\left(A, r, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth.actual_positiveWordBall_weightedLyndon_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every finite linearly ordered A with 2<=Fintype.card A and every r with 1<=r, there are naturals C,N with 0<C such that for every n>=N, n^(weightedLyndonExponent A r) <= C*(positiveWordBall A r n).card.

## References

- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth.actual_positiveWordBall_weightedLyndon_lower_bound`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall](PositiveWordBall.md)
