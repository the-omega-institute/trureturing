# Three-leg Choi compression

## Abstract

The explicit three-string readout compresses each leg of a complex-linear map on the normalized GHZ projector to the same output-first Choi matrix.

Fix a common computational frame on an arbitrary finite nonempty complex coordinate space d. Three-copy coordinates are associated to the right. The normalized GHZ vector is the sum of the diagonal strings, divided by the square root of the cardinality of d. Its dyad is ghz, equivalently the unnormalized diagonal dyad divided by that cardinality.

The matrix readout sends the coordinate of a diagonal matrix unit to its single diagonal string. An off-diagonal output-input coordinate is sent to the sum of the three strings having the output label once and the input label twice. The selected leg is implemented by the existing matrix-map tensor product with the identity on both spectators, conjugated by the exchange of the first and selected positions. The same supplied complex-linear map acts in all three positions.

**Theorem 1.1 (Exact compression and readout geometry).**

Lean statement: `D5/S3/Quantum/Foundation/ThreeLegChoiCompression.three_leg_choi_detector`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ThreeLegChoiCompression.three_leg_choi_detector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Commentary.*

For every complex-linear matrix map and every real weight triple of sum one, compressing the weighted three-leg output of ghz by readout gives the unnormalized output-first Choi matrix divided by the cardinality of d. The statement needs neither Hermiticity preservation nor nonnegative weights. It therefore includes every nonnegative normalized triple and all three endpoint triples.

The GHZ dyad is positive and has trace one. The Gram matrix of readout is diagonal: diagonal matrix-unit coordinates have value one and off-diagonal coordinates have value three. Consequently readout is injective and three times the identity minus its Gram matrix is positive semidefinite. The readout is generally not an isometry.

Each individual leg has the form of the Choi matrix embedded by its repeated-label isometry, divided by the cardinality of d. The three embedding ranges intersect only on diagonal strings. The adjoint of readout is a left inverse of each embedding, which proves the compression. Positive output at this GHZ dyad gives positive Choi matrix by compression and positive rescaling. The existing rectangular Choi criterion then gives all-amplification complete positivity of the supplied matrix map.

This is the single-block readout of Quantum Origin V Lemma 82.2, together with its forward single-block CP consequence. The finite direct-sum fixed probe, every rectangular transition, endpoint selection of a positive leg, canonical CP of the whole direct-sum map, and positivity on the entire ordered three-copy cone in Theorem 82.3 require additional arguments. The common frame and repeated basis labels are mathematical data. No physical GHZ preparation, copying operation, callable leg, event realization, PRE bridge or full Omega assertion follows.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ThreeLegChoiCompression.three_leg_choi_detector`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](FiniteKrausRepresentation.md)
