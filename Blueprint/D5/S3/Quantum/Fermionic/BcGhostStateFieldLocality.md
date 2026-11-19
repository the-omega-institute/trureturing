# Actual ghost superlocality

## Abstract

Signed locality for every homogeneous state in the actual ghost Fock space.

SignedFieldNormalProductLocality supplies the signed commutator, signed normal-product locality and divided-derivative locality. Reflection of the coefficient indices transports the flip law from BinomialKernelDelta. The actual ghost CAR and occupation-word induction specialize this generic calculus to the original Fock carrier.

**Theorem 1.1 (Homogeneous all-state signed locality).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostStateFieldLocality.stateField_locality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostStateFieldLocality.stateField_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The locality order is uniform in the vector on which the modes act. Actual b and c CAR, divided derivatives and signed Dong closure give locality of sorted creator words. Finite occupation support and actual parity extend this to every homogeneous finite linear combination. The statement is algebraic formal-field locality, without a physical spacetime interpretation.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostStateFieldLocality.stateField_locality`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostStateField](BcGhostStateField.md)
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProductLocality](../../VertexAlgebra/FieldNormalProductLocality.md)
