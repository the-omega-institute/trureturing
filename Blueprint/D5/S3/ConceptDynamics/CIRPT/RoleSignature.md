# CIRPT Four-Role Signatures

## Abstract

Four Boolean role coordinates classify every finite off-diagonal state pair.

**Definition 1.1 (Role coordinate).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOrdinal`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOrdinal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each CIRPT primitive role receives its canonical coordinate in Fin 4.

**Definition 1.2 (Coordinate decoder).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOfOrdinal`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOfOrdinal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A four-bit coordinate decodes to its corresponding primitive role.

**Definition 1.3 (Axis separation).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separatesOnAxis`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separatesOnAxis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Axis separation detects whether a matching atom rejects the supplied pair.

**Definition 1.4 (Role signature).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.roleSignature`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/RoleSignature.roleSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The role signature records axis separation at each of the four coordinates.

**Definition 1.5 (Ordered off-diagonal pairs).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.offDiagonalPairs`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/RoleSignature.offDiagonalPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generic finite carrier contains all ordered pairs with distinct entries.

**Definition 1.6 (Axis separation pairs).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separationPairsOnAxis`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separationPairsOnAxis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finset filters off-diagonal pairs by separation on one role axis.

**Definition 1.7 (Signature histogram).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.signatureHistogram`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/RoleSignature.signatureHistogram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The histogram counts ordered off-diagonal pairs with each exact signature.

**Theorem 1.8 (Coordinate decoding returns the role).**

$$\forall axis, \operatorname{axisOfOrdinal}(\operatorname{axisOrdinal}(axis)) = axis.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOfOrdinal_axisOrdinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Encoding and then decoding any primitive role returns that role.

**Theorem 1.9 (Axis separation reflects an atom witness).**

$$\operatorname{separatesOnAxis}(b, role, x, y) = true \iff \exists i, \operatorname{axis}(\operatorname{atom}(b, i)) = role \land \neg\operatorname{relation}(\operatorname{kernel}(\operatorname{atom}(b, i)), x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separatesOnAxis_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean axis test is true exactly when a matching atom rejects the pair.

**Theorem 1.10 (Agreement is the zero signature).**

$$\operatorname{agrees}(b, x, y) \iff \operatorname{roleSignature}(b, x, y) = \lambda coordinate, false.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/RoleSignature.agrees_iff_roleSignature_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bundle relates a pair exactly when none of its four roles separates it.

**Theorem 1.11 (Role signatures partition off-diagonal pairs).**

$$\sum_{s} \operatorname{signatureHistogram}(b, s) = \operatorname{card}(\operatorname{offDiagonalPairs}(X)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/RoleSignature.four_role_signature_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing all exact signature classes recovers the complete off-diagonal carrier.

**Theorem 1.12 (Histogram role counts are exact).**

$$\sum_{s: \operatorname{s}(\operatorname{axisOrdinal}(axis)) = true} \operatorname{signatureHistogram}(b, s) = \operatorname{card}(\operatorname{separationPairsOnAxis}(b, axis)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/RoleSignature.signature_histogram_axis_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing classes with one role bit set recovers that axis separation count.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.agrees_iff_roleSignature_zero`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOfOrdinal`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOfOrdinal_axisOrdinal`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.axisOrdinal`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.four_role_signature_partition`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.offDiagonalPairs`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.roleSignature`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separatesOnAxis`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separatesOnAxis_eq_true_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.separationPairsOnAxis`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.signatureHistogram`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/RoleSignature.signature_histogram_axis_count`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle](PrimitiveBundle.md)
