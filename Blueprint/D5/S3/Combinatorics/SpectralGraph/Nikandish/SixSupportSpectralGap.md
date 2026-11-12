# SixSupportSpectralGap

## Abstract

Complete received real spectral separation on the actual six-support operator.

**Definition 1.1 (below).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.below`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.below` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The complete actual quotient characteristic multiset, counted with algebraic multiplicity below a real cutoff.

**Theorem 1.2 (shifted_roots).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.shifted_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.shifted_roots` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Exact negative and zero inertia of the full shifted symmetric representative equals the actual quotient root count below the shift and its multiplicity. Consumed by the endpoint-one spectrum proof, including singular principal blocks.

**Theorem 1.3 (pair_sum_count).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.pair_sum_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.pair_sum_count` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every ordered positive real triple, at least three actual quotient eigenvalues lie strictly below a+b. The full-rank inertia pullback uses the actual symmetric representative and an explicit negative three-plane.

**Theorem 1.4 (total_sum_count).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.total_sum_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.total_sum_count` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For all ordered real2<=a<=b<=c, exactly three actual quotient roots lie strictly below s=a+b+c. The s-root has multiplicity one exactly at(2,2,2) and multiplicity zero everywhere else.

**Theorem 1.5 (upper_pair_sum_count).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.upper_pair_sum_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.upper_pair_sum_count` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For the same complete real domain, exactly three actual quotient roots lie below b+c and none equals b+c.

**Theorem 1.6 (result).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.result` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The complete global pair-sum and total-sum separation, with root multiplicities and the unique repeated boundary retained. Existing quotient_geometry supplies the positive semidefinite operator and simple zero kernel. These global results do not by themselves discharge all endpoint-one residual root assertions in L10.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.below`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.pair_sum_count`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.shifted_roots`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.total_sum_count`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap.upper_pair_sum_count`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/SixSupportInertiaIntervals](SixSupportInertiaIntervals.md)
- Dependency: [D5/S3/Weil/ZetaLinear/FullRankInertiaPullback](../../Weil/ZetaLinear/FullRankInertiaPullback.md)
