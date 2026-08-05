# Geometric Weights No-Go

## Abstract

No nonzero rational rescaling of geometric weights matches every singleton W weight.

**Theorem 1.1 (Geometric weights do not match singleton W weights).**

$\neg\exists\,w_1,\Lambda,c\in\mathbb{Q},\ c\neq0:\ w_1\Lambda^k=cF_{k+2}\ \text{for every }k\ge0.$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/GeometricWeights.no_geometric_weights_match_zeckendorf_singletons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The W-digit convention defines wValue k as fib(k+2), so singleton bits have weights 1, 2, 3 at indices 0, 1, 2. The first two equations force the geometric ratio to be 2, while the third requires its square to be 3; the nonzero scale excludes cancellation.

## References

- Truth anchor: `D5/S0/Conventions/GeometricWeights.no_geometric_weights_match_zeckendorf_singletons`
- Dependency: [D5/S0/Conventions/WDigits](WDigits.md)
