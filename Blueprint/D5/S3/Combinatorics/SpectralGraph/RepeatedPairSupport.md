# General-index paired support and the actual ideal graph

## Abstract

The complete repeated-pair support operator for every finite tail index set.

The source is the repeated-pair-product-tail note at PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, blob 66664013207b88567bf74f1a9a0c6eaf65d07f24. This module proves the full invariant embedding, with every support and arbitrary finite tail. Its operator is represented in the subset basis; no principal-compression eigenvalue claim is used. The existing four-index lift retains its original scope. The product-tail spectral criterion, its equality requirement of at least two tail coordinates, general Q3, and the three-prime integral-block boundary are separate obligations.

**Theorem 1.1 (All four paired-coordinate sectors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.sum_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.sum_four` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The complete finite-index sum decomposes into the four possibilities for the two paired coordinates and every remaining support. The full squarefree alternating operator proof consumes this shared helper.

**Theorem 1.2 (Disjointness on both coordinate sectors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.disjoint_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.disjoint_sum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Disjointness of two full disjoint-union supports is equivalent to disjointness in both coordinate sectors. This helper is consumed by the full alternating support action.

**Theorem 1.3 (Paired values on all full supports).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.pairedValue_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.pairedValue_sum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every paired function value on a disjoint-union support has its exact sign in the two singleton sectors and vanishes in the other sectors; the actual squarefree invariant lift consumes this helper.

**Theorem 1.4 (Weighted symmetry on the whole tail).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.weighted_symmetry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.weighted_symmetry` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every finite tail and every real parameter, the full subset matrix becomes Hermitian after multiplication by the diagonal product weights. This statement does not assert positivity when weights vanish or are negative.

**Theorem 1.5 (Cancellation on the entire vertex set).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_lift_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_lift_sum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For all positive natural exponents and every tail function, equal paired support weights make its full exponent-box lift sum to zero. Empty and full supports and every zero-valued cell are included.

**Theorem 1.6 (A nonzero actual lift).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_lift_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_lift_nonzero` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every nonzero tail function has a nonzero graph lift for all positive natural exponents. The proof produces an actual proper nonempty support and invokes the complete support-fiber theorem.

**Theorem 1.7 (The complete invariant action).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_support_action`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_support_action` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every support and every natural exponent, the complement support operator acts on paired values by K minus the identity. The proof treats all four possibilities for the two repeated coordinates and the entire powerset of the arbitrary tail.

**Theorem 1.8 (Transport to actual ideals).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.actual_paired_eigenvalue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.actual_paired_eigenvalue` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every finite tail, distinct primes, positive natural exponents, and nonzero full K eigenvector, V+1-e is an eigenvalue of the actual nonzero-proper-ideal intersection graph. V=(a+1)^2 product(k_i+1)-2. The proof consumes nonzero and weighted-zero-sum evidence and the actual ideal/support isomorphism; it does not assume that a compression eigenvector is a graph eigenvector.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.actual_paired_eigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.disjoint_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.pairedValue_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_lift_nonzero`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_lift_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.paired_support_action`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.sum_four`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport.weighted_symmetry`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions](IdealIntersectionObstructions.md)
