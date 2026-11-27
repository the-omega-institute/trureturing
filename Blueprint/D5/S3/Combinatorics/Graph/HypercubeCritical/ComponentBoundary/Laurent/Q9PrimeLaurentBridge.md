# Prime weights and Laurent transport on the nine-cube

## Abstract

For a connected induced cubic subgraph of the nine-cube with a nonempty chosen parity side, a nonzero defect kernel at distinct prime weights detects the Laurent identity when every row on that side has a partition of the axes by neighbor direction triples.

**Theorem 1.1 (One prime specialization detects the Laurent identity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9PrimeLaurentBridge.prime_defect_kernel_iff_laurentIdentity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9PrimeLaurentBridge.prime_defect_kernel_iff_laurentIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each selected vertex, require its three opposite-parity neighbors' direction triples to partition the nine axes. Each exterior axis then occurs as the second axis of exactly one two-step path. Reversal of ordered paths expresses twice the defect quadratic form as a sum of squared edge residuals. A kernel makes every residual vanish. Distinct prime valuations turn the resulting weight ratios into integer exponent differences. Conversely, the Laurent potential gives a nonzero kernel whenever every real coordinate weight is nonzero, by monomial evaluation.

For Hong, Wu and Xia's Problem 2, the partition hypothesis remains an independent condition on the candidate component. See https://arxiv.org/html/2610.09483v1#Thmproblem2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9PrimeLaurentBridge.prime_defect_kernel_iff_laurentIdentity`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes](Q9LaurentDirectionTypes.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport](../PrimeContactTransport.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedSaturation](../Q9WeightedSaturation.md)
