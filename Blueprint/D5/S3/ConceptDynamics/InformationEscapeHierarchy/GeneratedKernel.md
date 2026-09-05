# Generated-Kernel Lattice

## Abstract

Extensional catalog kernels form a finite bounded lattice inside the generated closure.

**Definition 1.1 (Generated kernel relation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelRelation`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The landed selected-catalog indistinguishability relation is packaged with its existing equivalence and decision proofs.

**Definition 1.2 (Extensional kernel setoid).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelSetoid`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Selections are equivalent exactly when their relation truth tables agree at every ordered state pair.

**Definition 1.3 (Generated kernel).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratedKernel`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratedKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The node carrier is the quotient of finite selections by exact relation equality.

**Definition 1.4 (Generated node).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite selection maps to its extensional generated-kernel class.

**Definition 1.5 (Node relation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relation`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact relation descends through the quotient.

**Theorem 1.6 (Represented relation is catalog indistinguishability).**

$$\operatorname{relation}(\operatorname{generatedKernel}(C, S), x, y) \iff \operatorname{indistinguishable}(C, S, x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relation_generatedKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Definition 1.7 (Boolean node relation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relationB`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relationB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The landed Boolean indistinguishability table descends through the extensional quotient.

**Theorem 1.8 (Boolean relation reflection).**

$$\operatorname{relationB}(P, x, y) = true \iff \operatorname{relation}(P, x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relationB_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Definition 1.9 (Kernel refinement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.KernelRefines`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.KernelRefines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finer node relation is pointwise contained in a coarser node relation.

**Theorem 1.10 (Generated-kernel extensionality).**

$$\forall x, y, \operatorname{relation}(P, x, y) \iff \operatorname{relation}(Q, x, y) \Rightarrow P = Q.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Definition 1.11 (Escape at a node).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Escape is the finite set of off-diagonal pairs still related by the node kernel.

**Definition 1.12 (Edge capture).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCapture`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCapture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge captures the source escape pairs absent from its target.

**Theorem 1.13 (Node escape agrees with landed escape).**

$$\operatorname{escapeAt}(\operatorname{generatedKernel}(C, S)) = \operatorname{escapePairs}(C, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt_generatedKernel_eq_escapePairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.14 (Generator union computes meet).**

$$\operatorname{generatedKernel}(C, \operatorname{union}(S, T)) = \operatorname{inf}(\operatorname{generatedKernel}(C, S), \operatorname{generatedKernel}(C, T)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.15 (The generated lattice is finite).**

$$\operatorname{Finite}(\operatorname{GeneratedKernel}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_finite_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.16 (Top is the empty-selection kernel).**

$$\operatorname{top}(\operatorname{GeneratedKernel}(C)) = \operatorname{generatedKernel}(C, \operatorname{empty}()).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.top_eq_generatedKernel_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.17 (Bottom is the full-catalog kernel).**

$$\operatorname{bottom}(\operatorname{GeneratedKernel}(C)) = \operatorname{generatedKernel}(C, \operatorname{fullIndexSet}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.bot_eq_generatedKernel_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.18 (Meet is generator union).**

$$\operatorname{inf}(\operatorname{generatedKernel}(C, S), \operatorname{generatedKernel}(C, T)) = \operatorname{generatedKernel}(C, \operatorname{union}(S, T)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.inf_eq_generatedKernel_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.19 (Meet has the greatest-lower-bound law).**

$$\operatorname{IsGLB}(\operatorname{pair}(P, Q), \operatorname{inf}(P, Q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isGLB_inf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.20 (Internal join has the least-upper-bound law).**

$$\operatorname{IsLUB}(\operatorname{pair}(P, Q), \operatorname{sup}(P, Q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isLUB_sup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Definition 1.21 (Generator step).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratorStep`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratorStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step inserts one catalog generator into a representative and certifies downward refinement.

**Definition 1.22 (Strict generator step).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.StrictGeneratorStep`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.StrictGeneratorStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A generator step is strict exactly when reverse refinement fails.

**Definition 1.23 (Collapsed addition).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.CollapsedAddition`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.CollapsedAddition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A collapsed addition is a certified generator step whose endpoints are one extensional node.

**Theorem 1.24 (Generator insertion respects extensional equality).**

$$\operatorname{generatedKernel}(C, S) = \operatorname{generatedKernel}(C, T) \Rightarrow \operatorname{generatedKernel}(C, \operatorname{insert}(i, S)) = \operatorname{generatedKernel}(C, \operatorname{insert}(i, T)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatorStep_wellDefined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.25 (Escape is antitone on generator steps).**

$$\operatorname{GeneratorStep}(C, P, Q, i) \Rightarrow \operatorname{escapeAt}(Q) \subseteq \operatorname{escapeAt}(P).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escape_antitone_on_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.26 (Strict refinement exactly means nonempty capture).**

$$\operatorname{GeneratorStep}(C, P, Q, i) \Rightarrow \neg\operatorname{KernelRefines}(P, Q) \iff \operatorname{edgeCapture}(P, Q) \neq \operatorname{empty}().$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strict_kernel_iff_nonempty_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.27 (Strict refinement exactly means positive capture count).**

$$\operatorname{GeneratorStep}(C, P, Q, i) \Rightarrow \neg\operatorname{KernelRefines}(P, Q) \iff 0 < \operatorname{card}(\operatorname{edgeCapture}(P, Q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strict_kernel_iff_edgeCapture_card_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.CollapsedAddition`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratedKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratorStep`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.KernelRefines`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.StrictGeneratorStep`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.bot_eq_generatedKernel_full`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCapture`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt_generatedKernel_eq_escapePairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escape_antitone_on_step`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.ext`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelRelation`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelSetoid`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_finite_lattice`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_union`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatorStep_wellDefined`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.inf_eq_generatedKernel_union`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isGLB_inf`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isLUB_sup`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relation`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relationB`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relationB_eq_true_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relation_generatedKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strict_kernel_iff_edgeCapture_card_pos`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strict_kernel_iff_nonempty_increment`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.top_eq_generatedKernel_empty`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/EscapePairs](../InformationEscape/EscapePairs.md)
