# CIRPT Primitive Kernels

## Abstract

The four CIRPT primitive roles share one decidable equivalence-kernel interface.

**Definition 1.1 (Primitive axis).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.PrimitiveAxis`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.PrimitiveAxis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CUT, FLOW, ADMIT, and ANCHOR remain explicit role labels.

**Definition 1.2 (Decidable kernel).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.DecidableKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.DecidableKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A kernel packages a relation, its equivalence laws, and pairwise decidability.

**Definition 1.3 (CUT kernel).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.cutKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.cutKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The CUT kernel identifies states with equal readout values.

**Definition 1.4 (FLOW kernel).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.flowKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.flowKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete FLOW output is treated as a CUT readout.

**Definition 1.5 (ADMIT kernel).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.admitKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.admitKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ADMIT kernel compares admission truth values without deleting states.

**Definition 1.6 (ANCHOR kernel).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.anchorKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.anchorKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ANCHOR kernel compares pointed equality profiles.

**Theorem 1.7 (CUT relation reflection).**

$$\forall x, y, \operatorname{relation}\left(\operatorname{cutKernel}\left(q\right), x, y\right) \iff \operatorname{q}\left(x\right) = \operatorname{q}\left(y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.cutKernel_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructor relation reduces exactly to equality of CUT outputs.

**Theorem 1.8 (FLOW relation reflection).**

$$\forall x, y, \operatorname{relation}\left(\operatorname{flowKernel}\left(flow\right), x, y\right) \iff \operatorname{flow}\left(x\right) = \operatorname{flow}\left(y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.flowKernel_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The FLOW constructor exposes equality of complete outputs.

**Theorem 1.9 (ADMIT relation reflection).**

$$\forall x, y, \operatorname{relation}\left(\operatorname{admitKernel}\left(admit\right), x, y\right) \iff \operatorname{admit}\left(x\right) \iff \operatorname{admit}\left(y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.admitKernel_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ADMIT constructor exposes logical equivalence of truth values.

**Theorem 1.10 (ANCHOR relation reflection).**

$$\forall x, y, \operatorname{relation}\left(\operatorname{anchorKernel}\left(a\right), x, y\right) \iff x = a \iff y = a.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.anchorKernel_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ANCHOR constructor exposes equality of pointed profiles.

**Theorem 1.11 (Primitive kernels are equivalence relations).**

$$\operatorname{Equivalence}\left(\operatorname{relation}\left(\operatorname{cutKernel}\left(q\right)\right)\right) \land\\\operatorname{Equivalence}\left(\operatorname{relation}\left(\operatorname{flowKernel}\left(flow\right)\right)\right) \land\\\operatorname{Equivalence}\left(\operatorname{relation}\left(\operatorname{admitKernel}\left(admit\right)\right)\right) \land\\\operatorname{Equivalence}\left(\operatorname{relation}\left(\operatorname{anchorKernel}\left(a\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.primitive_kernel_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality kernels and truth-profile kernels are reflexive, symmetric, and transitive.

**Theorem 1.12 (CUT is the canonical concept kernel).**

$$\{(x,y) \mid \operatorname{relation}\left(\operatorname{cutKernel}\left(q\right), x, y\right)\} = \operatorname{conceptKernel}\left(\lambda u: Unit, q, ()\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.cutKernel_relation_eq_conceptKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton dependent concept family recovers exactly the CUT collision set.

**Theorem 1.13 (ADMIT Boolean readout).**

$$\forall x, y, \operatorname{relation}\left(\operatorname{admitKernel}\left(admit\right), x, y\right) \iff \operatorname{ker}\left(\lambda state, \operatorname{decide}\left(\operatorname{admit}\left(state\right)\right), x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.admitKernel_relation_iff_bool_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deciding the admission proposition into Bool preserves its kernel exactly.

**Theorem 1.14 (ANCHOR Boolean readout).**

$$\forall x, y, \operatorname{relation}\left(\operatorname{anchorKernel}\left(a\right), x, y\right) \iff \operatorname{ker}\left(\lambda state, \operatorname{decide}\left(state = a\right), x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.anchorKernel_relation_iff_bool_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deciding equality with the anchor into Bool preserves its kernel exactly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.DecidableKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.PrimitiveAxis`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.admitKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.admitKernel_relation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.admitKernel_relation_iff_bool_readout`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.anchorKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.anchorKernel_relation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.anchorKernel_relation_iff_bool_readout`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.cutKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.cutKernel_relation_eq_conceptKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.cutKernel_relation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.flowKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.flowKernel_relation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.primitive_kernel_equivalence`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
