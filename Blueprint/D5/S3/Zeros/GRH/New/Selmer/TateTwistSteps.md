# Tate Twist Steps

## Abstract

Tate Twist Steps

Cocycles in a Tate twist cost only local loss and odd classes.

**Theorem 1.1 (hasTriangleCost_tateTwist).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/TateTwistSteps.hasTriangleCost_tateTwist`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/TateTwistSteps.hasTriangleCost_tateTwist` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Assume IsPrimeTriangle. Let Z be a module of cocycles of O(−e)/ℓ^ν unramified off ℓ, the w_j, w̄_j, whose coboundaries are killed by cyc(γ)^{−e} − 1. If b bounds its local loss at ℓ plus length shaOdd, HasTriangleCost holds with ℓ^h, b.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/TateTwistSteps.hasTriangleCost_tateTwist`
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/CrystallineRank](CrystallineRank.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/RibetFirstOrder](RibetFirstOrder.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/TiltingLemma](TiltingLemma.md)
