# The Sixteen-Pair Oscillator Zero Mode

## Abstract

The sum of the sixteen moving oscillator zero modes has point spectrum 16/9+n/3 for natural n and a one-dimensional ground eigenspace.

The moving polynomial space has one factor for each of the sixteen complementary pairs used in the order-three P48q calculation. Each factor has the two nonzero residue grids, with native frequency k.val+1 and fractional frequency (k.val+1)/3. The pairing of opposite frequencies is that of Bakalov and Kac, arXiv:math/0402315v1, equation (4.23), as used in ThirdCoverComplement.

**Definition 1.1 (The zero mode on one selected factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.pairLZero`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.pairLZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Split each basis monomial into its selected pair and the remaining variables. Apply ThirdCoverComplement.fractionalVirasoro(0) to the selected part, rename its variables back into the full space, and multiply by the remaining monomial. Extend linearly.

**Theorem 1.2 (The other factors carry the identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.pairLZero_separated`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.pairLZero_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the product of arbitrary polynomials in the selected and remaining variables, the operator applies the one-pair zero mode to the selected polynomial and leaves the remaining polynomial as the second factor. Restriction of occupations gives the identity on pairs of monomials, and bilinearity extends it to all such products.

**Definition 1.3 (The sum of the sixteen lifted operators).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum pairLZero over Fin 16. This is the moving oscillator operator on the full polynomial space.

**Definition 1.4 (Total native occupation energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.totalOccupationEnergy`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.totalOccupationEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each occupied variable (i,k), sum its exponent times k.val+1. Summing the sixteen pair energies gives this total by currying the occupation vector. All variable frequencies are positive, so the total vanishes exactly at zero occupation.

**Theorem 1.5 (The weight of each occupation monomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PolynomialFockLZeroSpectrum.lZero_spectrum computes the native oscillator energy by the creation commutator and the vacuum action. On the ordinary vacuum slice of the cover splitting, ThirdCoverGroundSpectrum.fractionalVirasoro_zero_monomial gives a shift of 1/9 and one third of the pair occupation energy. The sixteen terms sum to 16/9 plus one third of the total occupation energy.

**Theorem 1.6 (Coefficientwise action on any polynomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding a polynomial over its finite support shows that the coefficient of each occupation is multiplied by the weight of that occupation.

**Theorem 1.7 (Exact point spectrum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_eigenvalue_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_eigenvalue_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero coefficient of an eigenvector forces its eigenvalue to equal 16/9+n/3 for that coefficient's natural occupation energy n. Conversely, put exponent n at the variable in pair zero with complement label zero and put exponent zero elsewhere. That variable has native frequency one, so the coefficient-one monomial has energy n.

**Theorem 1.8 (The vacuum line).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_ground_eigenspace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_ground_eigenspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An eigenvector at 16/9 can only have a nonzero coefficient at zero occupation. The constant polynomial 1 has that weight, so the eigenspace is its complex span.

**Theorem 1.9 (Ground multiplicity one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_ground_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_ground_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The span of the nonzero vacuum polynomial has complex dimension one.

**Theorem 1.10 (Minimum real eigenvalue).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real eigenvalue is at least 16/9 since n is natural, and the vacuum attains 16/9.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_eigenvalue_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_ground_eigenspace`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_ground_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_minimum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.fractionalLZero_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.pairLZero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.pairLZero_separated`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.totalOccupationEnergy`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum](ThirdCoverGroundSpectrum.md)
