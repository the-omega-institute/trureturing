# Support at a shared real cutoff

## Abstract

The common Chebyshev exponent sum

**Theorem 1.1 (The square, cube and fifth-root cutoffs).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents.psi_sub_roots_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents.psi_sub_roots_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t ≥ 2 choose N at least the natural floor of log(t)/log(2). Subtract θ(t) and the square, cube and fifth ψ cutoffs from ψ(t). Their common finite support gives a sum over exponents k from 6 through N. The term θ(t^(1/k)) has coefficient 1 minus the three divisibility indicators for 2, 3 and 5. All coefficients from degree two through degree five vanish.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents.psi_sub_roots_eq_sum`
