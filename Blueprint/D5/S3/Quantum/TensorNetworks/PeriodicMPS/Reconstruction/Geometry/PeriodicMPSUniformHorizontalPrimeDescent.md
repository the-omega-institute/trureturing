# Horizontal height-one primes of the native cofactor ideal

## Abstract

Horizontal height-one primes of the native cofactor ideal

**Theorem 1.1 (A horizontal prime survives passage to the ordered-root fraction field).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.generic_prime_of_horizontal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.generic_prime_of_horizontal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero contraction to the ordered-root polynomial ring keeps all nonzero root coefficients out of the prime. The localization extends the prime, preserves its height, and contracts back to it.

**Theorem 1.2 (The contraction to the parameter torus has height one).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.generic_torus_contraction_height`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.generic_torus_contraction_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite free monic quadratic tower gives going-down. Integral incomparability and the domain property give the lower bound on the contracted height.

**Theorem 1.3 (Projected resultants exclude the exact ordered native cofactors).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.no_horizontal_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.no_horizontal_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose two of the ten native maximal minors on the ordered chart. If each generic image is a linear form in the two indicated radicals, multiplication by a partial conjugate gives a scalar contraction. If the cleared bivariate numerators have two nonzero projected resultants, no horizontal prime of height one contains all ten cofactors.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.generic_prime_of_horizontal`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.generic_torus_contraction_height`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent.no_horizontal_prime`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbient](PeriodicMPSUniformVerticalAmbient.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/UniformHorizontalTwoProjections](../../../UniformHorizontalTwoProjections.md)
