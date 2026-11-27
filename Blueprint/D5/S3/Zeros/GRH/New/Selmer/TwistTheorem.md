# Twist Theorem

## Abstract

Twist Theorem

Boundedly many tied primes shorten Selmer groups; one anticyclotomic twist then does, controlling L-values.

**Theorem 1.1 (exists_anticyclotomic_twist).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/TwistTheorem.exists_anticyclotomic_twist`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/TwistTheorem.exists_anticyclotomic_twist` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let ρ_i be balanced up to β_i, val_k families, z inertial at S₀ off ℓ, v(μ(z) − 1) ≤ c, β_i + v det(ρ_i z − 1) + v det(ρ_i z^{−c} − 1) ≤ B_i < ∞, η > 0. Some I, ψ make ψ^d, 1 ≤ d ≤ m, twists (IsAuxTwist) raising v(val_k) by ≤ 8c + η, with ψ^dρ_i of Selmer length ≤ B_i + η.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/TwistTheorem.exists_anticyclotomic_twist`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/WeightCongruence/WeightCongruence](../../Lib/GaloisRep/WeightCongruence/WeightCongruence.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/RootsOfUnityPoints](RootsOfUnityPoints.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/TiltingLemma](TiltingLemma.md)
