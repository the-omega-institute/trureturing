# PairedIdealIntersectionLift

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.

**Definition 1.1 (The full paired exponent family).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.pairExponents`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.pairExponents` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The exponent vector is (a,a,b,c). Neither tail exponent is bounded above. The final actual graph theorems permit every prime permutation.

**Theorem 1.2 (Injective paired support construction).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_nonzero` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For each tail support T, assign h(T) to {0} union T and -h(T) to {1} union T; all other supports get zero. The positive member of each pair is a genuine nonempty proper support cell with positive weight, so any nonzero coordinate vector lifts to a nonzero graph vector.

**Theorem 1.3 (Exact zero sum of actual paired vectors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_sum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Each paired cell has the same positive multiplicity a times the product of the tail exponents in T. The two values cancel exactly, including the extension by zero across all universal vertices.

**Theorem 1.4 (Exact actual paired action).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_support_action`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_support_action` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The support-complement Laplacian on this subspace is K_a-I. The proof evaluates the full four-coordinate support algebra with symbolic exponents, including all zero cells and both removed endpoints. It enumerates the fixed support carrier, not a finite set of exponents.

**Theorem 1.5 (Actual paired spectral lift).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.actual_paired_eigenvalue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.actual_paired_eigenvalue` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

A nonzero eigenvector of K_a with eigenvalue kappa lifts to the actual ideal graph eigenvalue V+1-kappa, V=(a+1) squared (b+1)(c+1)-2. The paired vector has explicit zero sum, so the reflection is valid even if kappa-1 is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.actual_paired_eigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.pairExponents`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_nonzero`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_support_action`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions](PairedIdealIntersectionObstructions.md)
