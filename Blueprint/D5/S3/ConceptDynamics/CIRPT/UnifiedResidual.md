# Unified CIRPT Residual Calculus

## Abstract

Kernel difference is the common residual calculus for all four CIRPT roles.

**Definition 1.1 (Kernel residual).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.kernelResidual`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.kernelResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A residual contains pairs retained by the current kernel and rejected by the target kernel.

**Definition 1.2 (Identity kernel).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.identityKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.identityKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity readout packages the equality diagonal as a decidable kernel.

**Definition 1.3 (Absolute kernel escape).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.escapeOfKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.escapeOfKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Absolute escape specializes the residual to the identity target.

**Definition 1.4 (CUT defect).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.cutDefect`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.cutDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The CUT defect is the current CUT residual against a target readout kernel.

**Definition 1.5 (FLOW defect).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.flowDefect`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.flowDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The FLOW defect targets the observed complete flow output.

**Definition 1.6 (ADMIT defect).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.admitDefect`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.admitDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ADMIT defect targets equality of admission truth values.

**Definition 1.7 (ANCHOR defect).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.anchorDefect`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.anchorDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The symmetric ANCHOR defect targets equality of pointed profiles.

**Definition 1.8 (Bundle role defect).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.bundleRoleDefect`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.bundleRoleDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A role defect contains current-kernel pairs separated by at least one atom carrying that role.

**Theorem 1.9 (CUT residual is the canonical defect relation).**

$$\operatorname{kernelResidual}(\operatorname{cutKernel}(q), \operatorname{cutKernel}(T)) = \operatorname{defectRelation}(q, T).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.kernelResidual_cut_eq_defectRelation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing both kernels to CUT readouts recovers the imported canonical defect relation exactly.

**Theorem 1.10 (Absolute escape removes the diagonal).**

$$\operatorname{escapeOfKernel}(K) = \{(x, y) \mid \operatorname{relation}(K, x, y)\} \setminus \operatorname{diagonal}(X).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.escapeOfKernel_eq_sdiff_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity target removes precisely the equality diagonal from the current kernel.

**Theorem 1.11 (Residual extensionality).**

$$(\forall x, y, \operatorname{relation}(Kone, x, y) \iff \operatorname{relation}(Ktwo, x, y)) \land (\forall x, y, \operatorname{relation}(Lone, x, y) \iff \operatorname{relation}(Ltwo, x, y)) \Rightarrow \operatorname{kernelResidual}(Kone, Lone) = \operatorname{kernelResidual}(Ktwo, Ltwo).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.residual_extensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise equivalent current and target relations determine the same residual set.

**Theorem 1.12 (Joint-target residual is a union).**

$$(\forall x, y, \operatorname{relation}(joint, x, y) \iff \forall j, \operatorname{relation}(\operatorname{L}(j), x, y)) \Rightarrow \operatorname{kernelResidual}(K, joint) = \operatorname{bigcup}j \operatorname{kernelResidual}(K, \operatorname{L}(j)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.residual_joint_target_eq_iUnion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CIRPT-IE-006 holds for an arbitrary indexed target family and its joint kernel.

**Theorem 1.13 (Bundle joint-target residual is a union).**

$$\operatorname{kernelResidual}(K, \operatorname{toKernel}(b)) = \operatorname{bigcup}i \operatorname{kernelResidual}(K, \operatorname{kernel}(\operatorname{atom}(b, i))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.residual_joint_target_eq_iUnion_bundle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite primitive-bundle form is the engine corollary of CIRPT-IE-006.

**Theorem 1.14 (Four-role residual union).**

$$\operatorname{kernelResidual}(\operatorname{cutKernel}(q), \operatorname{cutKernel}(\lambda x, (\operatorname{T}(x), \operatorname{Q}(\operatorname{F}(x)), \operatorname{decide}(\operatorname{A}(x)), \operatorname{decide}(x = a)))) = \operatorname{union}(\operatorname{union}(\operatorname{union}(\operatorname{cutDefect}(q, T), \operatorname{flowDefect}(q, F, Q)), \operatorname{admitDefect}(q, A)), \operatorname{anchorDefect}(q, a)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.four_role_residual_eq_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The combined CUT, FLOW, ADMIT, and ANCHOR target has the exact union of role defects.

**Theorem 1.15 (Target postprocessing contracts residuals).**

$$\operatorname{kernelResidual}(K, \operatorname{cutKernel}(\operatorname{compose}(h, f))) \subseteq \operatorname{kernelResidual}(K, \operatorname{cutKernel}(f)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.postprocessing_residual_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A distinction surviving postprocessing already survives before postprocessing.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.admitDefect`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.anchorDefect`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.bundleRoleDefect`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.cutDefect`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.escapeOfKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.escapeOfKernel_eq_sdiff_diagonal`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.flowDefect`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.four_role_residual_eq_union`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.identityKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.kernelResidual`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.kernelResidual_cut_eq_defectRelation`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.postprocessing_residual_mono`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.residual_extensional`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.residual_joint_target_eq_iUnion`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.residual_joint_target_eq_iUnion_bundle`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle](PrimitiveBundle.md)
- Dependency: [D5/S3/ConceptDynamics/Postprocessing/PostprocessingKernelMonotonicity](../Postprocessing/PostprocessingKernelMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
