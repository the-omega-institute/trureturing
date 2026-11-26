# Filtered channel restriction and a strict Bell bound

## Abstract

Input compression gives a filtered channel whose full Bell bound is strict.

**Theorem 1.1 (Three-dimensional counterexample).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellRestriction.threeByTwo_strict_bell_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellRestriction.threeByTwo_strict_bell_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized diagonal filter has three input levels and two environment levels. Its rows are (1/2, 3/2), (3/2, 1/2), and (1, 1). Its conditional trace-distance expansion is 3/4, while the Bell upper bound computed on the full input is 9/11. The inverse input marginal gives the lower bound. Compressing to the first two levels gives the matching upper bound because the compressed channel's admissible ratios also occur for the original channel.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellRestriction.threeByTwo_strict_bell_bound`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound](FilteredBellKernelUpperBound.md)
- Dependency: [D5/S3/Quantum/Information/PartialTrace/Isometries](../../Information/PartialTrace/Isometries.md)
