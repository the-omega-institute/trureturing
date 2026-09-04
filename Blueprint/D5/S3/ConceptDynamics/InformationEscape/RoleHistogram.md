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

$$\operatorname{roleHistogram}(C, i, s) = \operatorname{residualSignatureHistogram}(\operatorname{primitives}(\operatorname{theoremAt}(C, i)), \operatorname{withoutKernel}(C, i), s)$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each bucket counts an exact four-role residual signature.

**Theorem 1.3 (Unique capture is leave-one-out kernel residual).**

$$\operatorname{uniqueCapturePairs}(C, i) = \operatorname{kernelResidual}(\operatorname{withoutKernel}(C, i), \operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, i))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapturePairs_eq_kernelResidual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the finite residual and exact-count APIs.

**Theorem 1.4 (Unique capture has nonzero role signature).**

$$\operatorname{Member}(p, \operatorname{uniqueCapturePairs}(C, i)) \Rightarrow \operatorname{NotEqual}(\operatorname{residualRoleSignature}(\operatorname{primitives}(\operatorname{theoremAt}(C, i)), \operatorname{withoutKernel}(C, i), \operatorname{fst}(p), \operatorname{snd}(p)), (k \mapsto false))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapture_roleSignature_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen residual-signature bridge turns unique capture into nonzero role coverage.

**Theorem 1.5 (Unique capture is the union of its four active-role fibers).**

$$\operatorname{uniqueCapturePairs}(C, i) = \operatorname{biUnion}(\operatorname{univ}(Fin4), (k \mapsto \operatorname{filter}(\operatorname{uniqueCapturePairs}(C, i), (p \mapsto \operatorname{residualRoleSignature}(\operatorname{primitives}(\operatorname{theoremAt}(C, i)), \operatorname{withoutKernel}(C, i), \operatorname{fst}(p), \operatorname{snd}(p), k) = true))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapturePairs_eq_biUnion_roleFibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the finite residual and exact-count APIs.

**Theorem 1.6 (Nonzero buckets sum to unique capture).**

$$\operatorname{sum}(s, \operatorname{NotEqual}(s, (k \mapsto false)), \operatorname{roleHistogram}(C, i, s)) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram_sum_eq_uniqueCaptureCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fiberwise finite counting identifies the nonzero buckets with the residual finset.

**Theorem 1.7 (Theorem gain depends only on primitive kernels).**

$$(\forall j, x, y, \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, j))), x, y) \Leftrightarrow \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{apply}(U, j))), x, y)) \Rightarrow \operatorname{theoremGainRate}(\operatorname{withTheoremAt}(C, U), i) = \operatorname{theoremGainRate}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.theoremGain_depends_only_on_primitive_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the finite residual and exact-count APIs.

**Theorem 1.8 (Closed truth has zero unique capture).**

$$(\forall x, y, \operatorname{relation}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(C, i))), x, y) \Leftrightarrow \operatorname{relation}(\operatorname{cutKernel}((x \mapsto true)), x, y)) \Rightarrow \operatorname{uniqueCaptureCount}(C, i) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.closed_truth_uniqueCaptureCount_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the finite residual and exact-count APIs.

**Theorem 1.9 (Proof certificates do not enter unique capture).**

$$(\forall j, \operatorname{primitives}(\operatorname{theoremAt}(C, j)) = \operatorname{primitives}(\operatorname{apply}(U, j))) \Rightarrow \operatorname{uniqueCaptureCount}(\operatorname{withTheoremAt}(C, U), i) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.theoremAt_proof_irrelevant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the finite residual and exact-count APIs.

**Theorem 1.10 (Closed truth has universal kernel).**

$$\operatorname{relation}(\operatorname{cutKernel}((x \mapsto true))) = (x, y \mapsto True)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.closed_truth_cut_kernel_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the finite residual and exact-count APIs.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.closed_truth_cut_kernel_universal`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.closed_truth_uniqueCaptureCount_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.roleHistogram_sum_eq_uniqueCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.theoremAt_proof_irrelevant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.theoremGain_depends_only_on_primitive_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapturePairs_eq_biUnion_roleFibers`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapturePairs_eq_kernelResidual`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.uniqueCapture_roleSignature_nonzero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/RoleHistogram.withoutKernel`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/Laws](Laws.md)
