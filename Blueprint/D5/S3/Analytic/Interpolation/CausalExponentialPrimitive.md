# Exact causal primitive calculus

## Abstract

Finite causal primitives and square identities.

**Theorem 1.1 (The right-FTC square identity).**

Lean statement: `D5/S3/Analytic/Interpolation/CausalExponentialPrimitive.square_FTC`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/CausalExponentialPrimitive.square_FTC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact finite causal ramp and resolvent primitives supply the right derivatives and endpoint cancellations used by MomentExponentialCoercivity. The square FTC identity integrates the real part of conjugate(f) times its actual right derivative. Only helpers consumed by the existing Gamma, causal-Gram and growing-primitive proof paths are public. The original declaration namespaces and all theorem surfaces remain available by importing MomentExponentialCoercivity.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/CausalExponentialPrimitive.square_FTC`
- Dependency: [D5/S3/Analytic/Interpolation/AtomicPrefixEnergy](AtomicPrefixEnergy.md)
- Dependency: [D5/S3/Analytic/MomentOrthogonalPrimitiveGap](../MomentOrthogonalPrimitiveGap.md)
