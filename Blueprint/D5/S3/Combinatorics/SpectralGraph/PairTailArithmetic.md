# Exact tail equations, positive roots and contiguous offset cutoffs.

## Abstract

Exact tail equations, positive roots and contiguous offset cutoffs.

Sources: the complete large-tail, quadratic-tail-reduction, harmonic-tail and unique-tail notes at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The actual weighted four-cell tensor and ideal-graph lift are used throughout. Complete original attribution, antecedents, finite controls, failed-method and reproduction boundaries remain unchanged. Necessary root conditions are not sufficient integrality conditions. General single-pair, fully unequal and higher-prime Q3 remain open, and academic approval/publication remains separate.

**Theorem 1.1 (The entire unrestricted quadratic identity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.determinant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.determinant` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The determinant identity holds in every commutative ring before restrictions on any parameter. The algebraic constant at c=0 is not a positive ideal exponent.

**Theorem 1.2 (A nonzero constant throughout every candidate window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.H_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.H_positive` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every positive ordered-ring a,b,t with t<(a+1)b has the exact positive source constant. This proves the integer candidate polynomial is nonzero.

**Theorem 1.3 (All thirty-four positive coefficient terms).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.B_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.B_positive` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All integer offsets b<t<2b and a>=1 retain the complete source positive expansion, with no bound on either exponent.

**Theorem 1.4 (At most one positive integer root at each harmonic offset).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.positive_root_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.positive_root_unique` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Two positive integer tails at the same offset coincide. A nonnegative leading coefficient excludes all positive roots.

**Theorem 1.5 (The exact unique positive real root).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.positive_real_root`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.positive_real_root` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

When the leading coefficient is negative, the original positive square-root formula gives the unique positive real root of the full determinant. Integrality, divisibility, c>b and the other graph eigenvalues remain independent necessary checks.

**Theorem 1.6 (The unique continuous leading-coefficient cutoff).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.leading_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.leading_cutoff` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>0,b>=1 there is a cutoff tau strictly between b and 2b. At every t>=b the leading coefficient is negative exactly when t<tau. The integer source domain is included, with no claim about excluded smaller real b.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.B_positive`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.H_positive`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.determinant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.leading_cutoff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.positive_real_root`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailArithmetic.positive_root_unique`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants](PairedIdealIntersectionDeterminants.md)
