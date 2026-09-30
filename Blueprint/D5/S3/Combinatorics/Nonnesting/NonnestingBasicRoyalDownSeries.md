# Quadratic Equation for Downstep Weights

## Abstract

The downstep-weighted generating function satisfies a quadratic equation.

**Theorem 1.1 (Downstep series equation).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownSeries.downSeries_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownSeries.downSeries_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Let D be the ordinary generating function whose coefficient of x to the power n is the downstep weight sum at semilength n. Then 1 - (1 + x)D + 2xD squared equals zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownSeries.downSeries_quadratic`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownCount](NonnestingBasicRoyalDownCount.md)
