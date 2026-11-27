# Hecke String

## Abstract

Hecke String

Weak lifts: Hecke polynomial is the string times a factor integral after normalising.

**Theorem 1.1 (eventually_heckePoly_eq_string_mul).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/HeckeString.eventually_heckePoly_eq_string_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/HeckeString.eventually_heckePoly_eq_string_mul` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let the normalised representation u of an eigenform have integral characteristic polynomials, all with root 1. At generic geometric Frobenii σ (mostFrobenii): if char u(σ) ≡ S·∏_{i<n−r}(X − cyc(σ)^{−i}) with ‖S(1)‖ ≥ 1, the rescaled Hecke polynomial is ∏_{i<n−r}(X − q^i)·T, and ιT divides an integral e with e(1) = 1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/HeckeString.eventually_heckePoly_eq_string_mul`
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/HeckeStableSubspaces](HeckeStableSubspaces.md)
