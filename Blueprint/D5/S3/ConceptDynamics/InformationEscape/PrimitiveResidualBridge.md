# Primitive Residual Bridge

## Abstract

Catalog unique capture is the canonical CIRPT primitive-kernel residual.

**Theorem 1.1 (Unique capture is leave-one-out kernel residual).**

$$\operatorname{uniqueCapturePairs}(C, i) = \operatorname{kernelResidual}(\operatorname{withoutKernel}(C, i), \operatorname{primitiveKernel}(C, i))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.uniqueCapturePairs_eq_kernelResidual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof specializes the frozen CIRPT and finite information-escape kernels.

**Theorem 1.2 (Theorem gain depends only on primitive kernels).**

$$\operatorname{PointwiseKernelEqual}(C, U) \Rightarrow \operatorname{theoremGainRate}(\operatorname{withTheoremAt}(C, U), i) = \operatorname{theoremGainRate}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.theoremGain_depends_only_on_primitive_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof specializes the frozen CIRPT and finite information-escape kernels.

**Theorem 1.3 (Closed truth has universal kernel).**

$$\operatorname{relation}(\operatorname{cutKernel}(\operatorname{constantTrue}(X))) = \operatorname{UniversalRelation}(X)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.closed_truth_cut_kernel_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof specializes the frozen CIRPT and finite information-escape kernels.

**Theorem 1.4 (Closed truth has zero unique capture).**

$$\operatorname{ClosedTruthKernel}(C, i) \Rightarrow \operatorname{uniqueCaptureCount}(C, i) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.closed_truth_uniqueCaptureCount_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof specializes the frozen CIRPT and finite information-escape kernels.

**Theorem 1.5 (Proof certificates do not enter unique capture).**

$$\operatorname{PrimitiveFamiliesEqual}(C, U) \Rightarrow \operatorname{uniqueCaptureCount}(\operatorname{withTheoremAt}(C, U), i) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.theoremAt_proof_irrelevant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof specializes the frozen CIRPT and finite information-escape kernels.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.closed_truth_cut_kernel_universal`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.closed_truth_uniqueCaptureCount_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.theoremAt_proof_irrelevant`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.theoremGain_depends_only_on_primitive_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge.uniqueCapturePairs_eq_kernelResidual`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/Laws](Laws.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RoleHistogram](RoleHistogram.md)
