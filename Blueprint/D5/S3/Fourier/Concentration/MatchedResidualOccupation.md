# Weight of matched occupations

## Abstract

A pointwise matching controls a subset of the weighted occupation pairs.

**Theorem 1.1 (Multinomial mass under a pointwise matching).**

$$\sum_{(a,b) \in S} c_{d}(a) c_{d}(b) \leq d! R^{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/MatchedResidualOccupation.matched_occupation_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be finite with nonnegative real weights w. Let E be a relation on J. The sum of w(i)w(j) over ordered edges of E is denoted by R. Let S be a set of ordered pairs of degree-d count vectors. Each pair in S has representative words whose corresponding letters lie in E. The function c with subscript d denotes the weighted multinomial coefficient.

For either count vector, all representative words differ only by a permutation. Thus every pair of representative words admits some matching. Their weights sum to the product of the two multinomial coefficients.

Sum over all position permutations. Each matchable word pair contributes its nonnegative weight at least once. For a fixed permutation, the two words are equivalent to a length-d word of ordered pairs of letters. Each position contributes the same edge mass R. There are d factorial permutations.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/MatchedResidualOccupation.matched_occupation_mass_le`
- Dependency: [D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow](FiniteTailMomentMissingWindow.md)
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../../Quantum/Entanglement/OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Schatten/MatrixSimilarity](../../Quantum/Schatten/MatrixSimilarity.md)
