# Specialization of the monic literal jet

## Abstract

Specialization of the monic literal jet

**Theorem 1.1 (The split remainder equals the Hermite interpolant).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.literalJetRemainder_eq_hermite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.literalJetRemainder_eq_hermite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At distinct nodes, explicit Hermite cardinal interpolation and monic division define the same polynomial.

**Theorem 1.2 (Coefficient specialization commutes with the invariant remainder).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_map`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Division by the squared invariant characteristic preserves the literal jet under any coefficient ring homomorphism.

**Theorem 1.3 (The invariant remainder at the fourfold collision).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the colliding invariant values, scaling by four to the residual length gives the binomial polynomial truncated at degree seven.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_collision`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.invariantLiteralJet_map`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLiteralJetSpecialization.literalJetRemainder_eq_hermite`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCollisionTaylor](PeriodicMPSUniformCollisionTaylor.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHermiteLiteralJet](PeriodicMPSUniformHermiteLiteralJet.md)
