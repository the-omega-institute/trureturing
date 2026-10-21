# Actual Gamma form core: LatticeBoundary

## Abstract

For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier.

**Definition 1.1 (actualIocBoundaryPair).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier.

**Theorem 1.2 (actualIocBoundaryPair nat tendsto).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_nat_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_nat_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier.

**Theorem 1.3 (Uniform bound for every image and cutoff).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_abs_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_abs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and every complex L2 profile on (-a,a], the absolute real boundary pairing is at most C(a) times its squared L2 norm, uniformly in the real cutoff. Here C(a)=2*pi/(1-exp(-2))+4*a*exp(-a)/((1-exp(-a))*(1-exp(-4*a))). The integral is absolutely integrable: the nearest images use the Carleman bound, and all remaining integer images use a geometric majorant.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_abs_le`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_nat_tendsto`
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](../../TestFunctions/ConvolutionSquarePositivity.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../ArchimedeanJumpDecomposition.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/CornerTransport](CornerTransport.md)
- Dependency: [D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport](../PeriodicEnergyTransport.md)
