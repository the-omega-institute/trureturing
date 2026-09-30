# Finite Cubic Recovery

## Abstract

Finite cubic data recover the normalized product and its stabilizer.

This document formalizes the finite algebra step behind the cubic response interface. It uses Fin n coordinates for the unit complement and does not construct a VOA, a Monster action, or the Griess tensor.

**Theorem 1.1 (Full multiplication recovery).**

Lean statement: `D5/S3/VertexAlgebra/FiniteCubicRecovery.mul_eq_recoveredMul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FiniteCubicRecovery.mul_eq_recoveredMul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x = ae + u and y = be + v, the product is recovered from the invariant form and the cubic sharp tensor as (ab + <u,v>/3)e + av + bu + T sharp(u,v). The normalization is the one used in the local completion discussion in M01.

**Theorem 1.2 (Cubic stabilizer criterion).**

Lean statement: `D5/S3/VertexAlgebra/FiniteCubicRecovery.extend_preserves_mul_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FiniteCubicRecovery.extend_preserves_mul_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An orthogonal map on the unit complement, extended by fixing the unit, preserves the recovered product exactly when it preserves the cubic sharp tensor. The actual Monster identification is an external Griess-algebra input.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FiniteCubicRecovery.extend_preserves_mul_iff`
- Truth anchor: `D5/S3/VertexAlgebra/FiniteCubicRecovery.mul_eq_recoveredMul`
