# Canonical cyclic field of a Lucas block

## Abstract

The native Lucas block defines a canonical cyclic cubic.

**Theorem 1.1 (Native Eisenstein and polynomial discriminant certificates).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic.native_polynomial_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic.native_polynomial_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The monic depressed cubic attached to the block has a square polynomial discriminant. Translating the root by one gives an Eisenstein certificate at three, proving irreducibility without a square-times-cube hypothesis.

**Theorem 1.2 (The native splitting field is cyclic cubic).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic.native_cyclic_field`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic.native_cyclic_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square discriminant appears concretely in the other two roots as a rational function of the first. It follows that the splitting field already has degree three and its Galois group is cyclic.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic.native_cyclic_field`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic.native_polynomial_certificate`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein](GoldenCubicThueEisenstein.md)
