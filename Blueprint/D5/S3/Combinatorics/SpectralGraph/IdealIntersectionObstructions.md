# IdealIntersectionObstructions

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.

**Definition 1.1 (Spectrum of the actual finite ideal graph).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.HasActualEigenvalue`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.HasActualEigenvalue` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

This predicate uses the Laplacian on the actual nonzero proper ideals. Its finite structure comes from the finite underlying ring; no quotient or desired spectral bridge is assumed in the definition.

**Definition 1.2 (Actual Laplacian integrality).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.ActualLaplacianIntegral`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.ActualLaplacianIntegral` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every real Laplacian eigenvalue of the actual ideal graph is an integer. Symmetry of the real Laplacian gives the usual spectral interpretation.

**Theorem 1.3 (Actual graph spectral reflection).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.actual_eigenvalue_of_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.actual_eigenvalue_of_support` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

A nonzero support-model complement eigenvector with total sum zero yields the actual ideal-graph eigenvalue V minus the complement eigenvalue. This uses the proved graph isomorphism and the identity L(G)+L(complement G)=V I-J. The intermediate complement eigenvalue is allowed to be zero.

**Theorem 1.4 (Distinguished-exponent threshold, including equality).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.threshold_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.threshold_obstruction` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Let m=k_d, A be the product of the other exponents, P the product of their successors and B=P-1-A. For at least three prime coordinates, A at least (m squared minus one)B minus (m minus one) gives an actual eigenvalue strictly between V-1 and V. The denominator-free trial has cell values m(m+1)B, (m-1)(m+1)B and -m(A+m-1), with zero mean. Energy minus norm squared factors as m B times ((m squared minus one)B-A-(m-1)) times (m A+(m squared minus one)B+m(m-1)). The weak threshold gives a nonpositive Rayleigh defect. At equality, a nonempty support containing d and another coordinate has trial action zero and nonzero trial value. Hence the trial is not a unit eigenvector; the Hermitian expansion still gives a strictly smaller positive eigenvalue. All prime permutations, m=1 and zero universal count are included.

**Theorem 1.5 (Unit exponent for every prime count at least three).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.unit_exponent_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.unit_exponent_obstruction` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The threshold theorem at m=1 applies for any distinguished unit coordinate and arbitrary positive remaining exponents. Thus the actual ideal graph has an eigenvalue in (V-1,V), and is not Laplacian integral. Taking every exponent equal to one gives the squarefree specialization; its exact application is checked transiently.

**Theorem 1.6 (Reciprocal condition through the threshold).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.reciprocal_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.reciprocal_obstruction` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For m=k_d at least two, sum of 1/k_i over the other coordinates at most 1/m squared implies the full threshold. The product inequality converts the reciprocal hypothesis into A at least (m squared minus one)B minus (m-1). The theorem consumes the threshold result and repeats no Rayleigh proof. If every other k_i is at least m squared times (t-1), each reciprocal is at most 1 divided by that common bound; summing t-1 terms proves the hypothesis. This unbounded-coordinate application is checked transiently.

**Theorem 1.7 (Sharp two-prime unit boundary).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.two_prime_unit_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.two_prime_unit_integral` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

With precisely two distinct primes and one unit exponent, the complement is a star together with isolated universal vertices. A star on a center and A leaves has Laplacian eigenvalues among zero, one and A+1. Complement reflection therefore gives only integer actual eigenvalues, including the other exponent A=1. The higher-prime obstruction starts sharply at three prime factors.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.ActualLaplacianIntegral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.HasActualEigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.actual_eigenvalue_of_support`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.reciprocal_obstruction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.threshold_obstruction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.two_prime_unit_integral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions.unit_exponent_obstruction`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport](IdealIntersectionSupport.md)
