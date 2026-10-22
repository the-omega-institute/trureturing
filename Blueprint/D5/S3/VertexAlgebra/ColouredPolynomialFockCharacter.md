# Finite-Colour Oscillator Character

## Abstract

Finite-colour oscillator energy fibers are partition profiles and have the powered Euler character.

Let C be an arbitrary finite type, including the empty type. An oscillator occupation is a finitely supported function on C × Nat with natural values. The oscillator indexed by (c, n) has weight n + 1. EnergyFiber C N is the actual fiber of the sum of these weighted occupations, not a space defined by its desired dimension. A partition profile consists of a finite energy allocation to the colours, with total N, and one integer partition of each allocated energy.

**Theorem 1.1 (Concrete occupations and partition profiles).**

Lean statement: `D5/S3/VertexAlgebra/ColouredPolynomialFockCharacter.energyFiberEquivPartitionProfile`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ColouredPolynomialFockCharacter.energyFiberEquivPartitionProfile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Currying restricts the occupation vector to each colour. The exact existing PolynomialFockCharacter.energyFiberEquivPartition converts each restriction into a partition. The inverse uses those same one-colour inverses and uncurries the resulting finitely supported family. The weighted sum equals the sum of the colour energies. The allocation lies in Mathlib's finite finsuppAntidiag univ N; this also proves finiteness without any finite occupation cutoff. Both inverse computations and the energy equation apply to every N and to empty C.

**Theorem 1.2 (Coefficientwise finite product and Euler power).**

Lean statement: `D5/S3/VertexAlgebra/ColouredPolynomialFockCharacter.character_euler_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ColouredPolynomialFockCharacter.character_euler_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of character C at N is Nat.card (EnergyFiber C N), cast to Complex. Cardinality of the partition-profile sigma is the finite sum, over the antidiagonal of allocations, of products of partition cardinalities. PowerSeries.coeff_prod gives exactly this convolution. Thus the character equals the finite product of the existing one-colour zero-mode characters, and therefore the existing Euler tprod raised to card C. Only a finite product is interchanged with coefficients. The established one-colour theorem owns the infinite formal product and its unit inversion. No analytic convergence or new infinite interchange is asserted. These are standard partition identities; the contribution is the concrete occupation-to-profile and coefficient bridge, not a claim of mathematical novelty.

Application to the actual transverse native basis. For LatticeData D and axes xAxis, yAxis : Fin D.rank, use the actual colour type {i : Fin D.rank // i != xAxis and i != yAxis}. The native transverseLevelIndex requires every occupation on either axis to vanish, the polarized ghost subset to be contained in {3}, and nativeLevel to equal the prescribed integer level. Restriction to the colour complement and extension by zero are inverse operations on the oscillator occupations. The two allowed ghost subsets are empty and {3}; both have polarized energy zero. Consequently the actual level-N index, for N nonnegative, is equivalent to EnergyFiber C N × Bool. Empty corresponds to ghost number J = 1 and {3} to J = 2, by the accepted transverseLevelWord_J_degree theorem. The absolute range-P character includes both partners: 2 times the coloured character. In particular level zero has dimension 2, not 1.

Compose this actual index equivalence with OriginalQQuartetSource.nativeTransverseEnergy_finrank. Its space is the intersection of the charge-beta range, the actual quartet projection range, and the kernel of M 0 + G 0 minus (chosenH beta + level - 1) times the identity. Every application retains H * gramComplex D = 1, gramComplex D * H = 1, inverse * frame = 1 and frame * inverse = 1. No positivity, distinct-axis condition or invertibility assumption is silently inserted. The general formula keeps card C. Only with rank 26 and distinct axes does card C equal 24, yielding 2 times the Euler product to the twenty-fourth power. Negative integer levels have empty index and zero space by the accepted negative-level supplier. Applying the physical mass-shell relation level = 1 - chosenH beta requires the exact level correspondence and its nonnegativity. Automatic nonnegativity is not asserted.

Limits of the character statement. The bivariate basis count has the formal expression (u + u^2) times the coloured oscillator character. A basis count is not a proof of original-Q quotient ghost multiplicities: that requires the actual quotient and its homogeneous representative and boundary arguments. Positive isometry and no-ghost, a vacuum shift or eta-to-Monster-J identification, Vnatural, fusion and anomaly structures, full string dynamics and the spacetime or AdS/CFT reconstruction remain separate open obligations. Native and rank-26 specializations are transient exact applications, not new retained wrappers.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ColouredPolynomialFockCharacter.character_euler_product`
- Truth anchor: `D5/S3/VertexAlgebra/ColouredPolynomialFockCharacter.energyFiberEquivPartitionProfile`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockCharacter](PolynomialFockCharacter.md)
