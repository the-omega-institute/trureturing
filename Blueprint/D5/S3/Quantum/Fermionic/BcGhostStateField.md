# The actual ghost state-field construction

## Abstract

Actual signed occupation-word ghost fields on the full countable Fock carrier.

The carrier, vacuum, occupation creators, CAR and parity are exactly those of CountableOccupationFock and BcGhostFock. An ascending occupation list gives nested divided derivatives of the physical b and c fields. A reverse-ordered normal-product half carries the sign determined by the tail length. This construction defines a linear map on every finitely supported occupation state and does not replace the carrier by a finite cutoff.

The bounded-pole and normal-product arguments adapt the existing FieldNormalProduct construction, attributed there to Scott Carnahan's vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea. The signed half is constructed directly; ordinary plus ordering is not asserted to be fermionic normal ordering.

**Theorem 1.1 (All-state creation and the exact physical generators).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_creation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minus-one coefficient creates every actual state, every nonnegative coefficient annihilates the vacuum, and the vacuum field is the identity field. The generating states are the singleton occupations zero and one. Their normalized vertex modes are respectively the physical b mode shifted by minus one and c mode shifted by plus two.

**Theorem 1.2 (Covariance for the original ghost translation).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_translation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The translation is BcGhostVirasoro.L at minus one. Its vacuum value vanishes, and its commutator with every state-field mode is the formal derivative coefficient. The proof uses the original b and c Ward identities, the integer binomial shift and the signed finite-sum telescope; no translation operator is supplied as an assumption.

**Theorem 1.3 (Parity on the full state space).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by occupation parity intertwines every state-field coefficient with the field of the parity-transformed state. This holds for arbitrary inhomogeneous finite sums and specializes to the homogeneous sign through linearity.

The companion BcGhostStateFieldLocality and BcGhostStateFieldIterate modules establish homogeneous all-state signed locality and the signed all-integer iterate law with finite coefficient sums. This document does not identify the conformal state with the existing ghost Virasoro field, the ghost cubic with a state zero mode, or prove the BRST derivation, physical bracket, no-ghost, string or AdS/CFT programme.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_creation`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_parity`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostStateField.stateField_translation`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostVirasoro](BcGhostVirasoro.md)
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProduct](../../VertexAlgebra/FieldNormalProduct.md)
