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

**Theorem 1.2 (One fixed probe detects every rectangular sector).**

Lean statement: `D5/S3/Quantum/Foundation/ThreeLegChoiCompression.direct_sum_three_leg_detector`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ThreeLegChoiCompression.direct_sum_three_leg_detector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Commentary.*

Let the original algebra be an arbitrary finite nonempty direct sum of full complex matrix algebras on finite nonempty coordinate types. The supplied complex-linear map may send each input block into every output block. The theorem imposes no Hermiticity, positivity, trace preservation, unitality or sector preservation premise. The stronger complex-linear statement includes the Hermiticity-preserving maps in Quantum Origin V Theorem 82.3.

The fixed probe is the sum of the normalized GHZ projectors in the iii sectors, weighted by the dimension of block i divided by the sum of all block dimensions. Every other ordered seed is zero. It is positive and its ordinary total trace over every ordered sector is one. Its definition depends on the common frames and dimensions, independently of the supplied map and weights.

For every nonnegative real weight triple of sum one, the weighted same-map lift sends this probe to a positive element if and only if the original map, transported by the matrix coordinates, is a canonical CompletelyPositiveMap. This is also equivalent to positivity of that actual lift on the entire ordered three-copy cone. Every block is an unrestricted positive semidefinite matrix; no separability condition is used. All scalar blocks, unequal block dimensions, repeated labels, rectangular transitions and endpoint weights are retained.

The diagonal iii output is the weighted single-block GHZ lift. Its readout compresses to the diagonal component Choi matrix divided by the total dimension. For a transition from i to a distinct j, any position with positive weight isolates the corresponding rectangular Choi matrix in the sector having j in that position and i in both spectators. The repeated-label rectangular embedding is proved isometric, and the other two positions are explicitly permuted into the same output-first coordinates. Compression and positive rescaling recover every rectangular Choi matrix.

The existing rectangular Choi theorem supplies component CP. The amplification bridge is proved for the original map: applying it entrywise to an arbitrary auxiliary matrix over the direct sum gives, in each output block, the sum of the amplified rectangular components. A star algebra equivalence flattens every central component of a canonical C-star auxiliary matrix. This proves equivalence with a canonical CompletelyPositiveMap whose linear map is precisely the transported original map. Conversely each actual leg is positive on all ordered sector matrices, and their nonnegative weighted sum preserves the whole cone.

The common frame and repeated basis labels are mathematical data. These mathematical readout results supply no physical GHZ preparation, copying operation, callable leg, event realization, PRE bridge or full Omega assertion. The later original-event and all-real intertwining contracts in Quantum Origin V remain separate obligations.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ThreeLegChoiCompression.direct_sum_three_leg_detector`
- Truth anchor: `D5/S3/Quantum/Foundation/ThreeLegChoiCompression.three_leg_choi_detector`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](FiniteKrausRepresentation.md)
