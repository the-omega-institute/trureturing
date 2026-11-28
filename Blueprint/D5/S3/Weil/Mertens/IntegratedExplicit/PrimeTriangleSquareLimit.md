# The prime-power correction of the prime triangle

## Abstract

The complete prime-power correction has an explicit square-root coefficient.

**Theorem 1.1 (Square-root coefficient of the prime-power contribution).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit.normalized_mangoldtHinge_sub_primeTriangle_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit.normalized_mangoldtHinge_sub_primeTriangle_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Mangoldt triangle minus the ordinary prime triangle, divided by the square root of its scale, tends to six times the square root of two minus eight. Exact prime-power decomposition isolates the squares. Abel summation and the prime number theorem give their limit. The contribution of higher powers vanishes at this scale.

**Theorem 1.2 (A fixed square-root allowance equivalent to RH).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit.rh_iff_eventual_prime_triangle_nine_tenths`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit.rh_iff_eventual_prime_triangle_nine_tenths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the quarter grid, RH is equivalent to the eventual lower bound 2 x log(2) minus nine tenths of the square root of x for the ordinary prime triangle. The square contribution gives the deterministic shift. The actual zero sum controls the remaining centered error under RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit.normalized_mangoldtHinge_sub_primeTriangle_tendsto`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit.rh_iff_eventual_prime_triangle_nine_tenths`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError](../../../Arith/Robin/PriceRecord/UniformThetaShellError.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound](RobinActualWeightedBound.md)
