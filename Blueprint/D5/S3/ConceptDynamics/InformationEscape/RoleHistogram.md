# Unique Capture Role Histogram

## Abstract

The leave-one-out residual is partitioned by four-bit CIRPT role signatures.

**Definition 1.1 (Leave-one-out catalog kernel).**

$$\operatorname{relation}(\operatorname{withoutKernel}(C, i)) = \operatorname{indistinguishable}(C, \operatorname{without}(C, i))$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.withoutKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The other theorem bundles form one decidable equivalence kernel.

**Definition 1.2 (Residual role-signature multiplicity).**

$$\operatorname{roleHistogram}(C, i, s) = \operatorname{residualSignatureHistogram}(\operatorname{withoutKernel}(C, i), s)$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each bucket counts an exact four-role residual signature.

**Theorem 1.3 (Unique capture has nonzero role signature).**

$$\operatorname{Member}(p, \operatorname{uniqueCapturePairs}(C, i)) \Rightarrow \operatorname{NotEqual}(\operatorname{residualRoleSignature}(C, i, p), z)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapture_roleSignature_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen residual-signature bridge turns unique capture into nonzero role coverage.

**Theorem 1.4 (Nonzero buckets sum to unique capture).**

$$\operatorname{sumNonzero}(\operatorname{roleHistogram}(C, i)) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram_sum_eq_uniqueCaptureCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fiberwise finite counting identifies the nonzero buckets with the residual finset.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram_sum_eq_uniqueCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapture_roleSignature_nonzero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.withoutKernel`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/RoleSignature](../CIRPT/RoleSignature.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ExactRate](ExactRate.md)
