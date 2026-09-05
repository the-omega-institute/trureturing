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

**Definition 1.9 (Boolean node equality).**

$$\operatorname{nodesEqB}(P, Q) = \operatorname{all}(\operatorname{StatePairs}(A), \operatorname{relationB}(P, x, y) = \operatorname{relationB}(Q, x, y)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.nodesEqB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete finite relation truth tables are compared by an executable fold.

**Theorem 1.10 (Boolean node equality reflection).**

$$\operatorname{nodesEqB}(P, Q) = true \iff P = Q.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.nodesEqB_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Definition 1.11 (Kernel refinement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.KernelRefines`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.KernelRefines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finer node relation is pointwise contained in a coarser node relation.

**Definition 1.12 (Escape at a node).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Escape is the finite set of off-diagonal pairs still related by the node kernel.

**Definition 1.13 (Edge capture).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCapture`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCapture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge captures the source escape pairs absent from its target.

**Theorem 1.14 (Node escape agrees with landed escape).**

$$\operatorname{escapeAt}(\operatorname{generatedKernel}(C, S)) = \operatorname{escapePairs}(C, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt_generatedKernel_eq_escapePairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Definition 1.15 (Node escape count).**

$$\operatorname{escapeCount}(P) = \operatorname{card}(\operatorname{escapeAt}(P)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The node escape count is the cardinality of its finite escape set.

**Definition 1.16 (Node escape rate).**

$$\operatorname{escapeRate}(P) = \frac{\operatorname{escapeCount}(P)}{\operatorname{escapeDenominator}(A)}.$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact node rate uses the canonical arena escape denominator.

**Definition 1.17 (Edge capture count).**

$$\operatorname{edgeCaptureCount}(P, Q) = \operatorname{card}(\operatorname{edgeCapture}(P, Q)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCaptureCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The edge capture count is the cardinality of the removed escape set.

**Definition 1.18 (Edge capture rate).**

$$\operatorname{edgeCaptureRate}(P, Q) = \frac{\operatorname{edgeCaptureCount}(P, Q)}{\operatorname{escapeDenominator}(A)}.$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCaptureRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact edge rate uses the canonical arena escape denominator.

**Theorem 1.19 (Node rate agrees with landed catalog rate).**

$$\operatorname{escapeRate}(\operatorname{generatedKernel}(C, S)) = \operatorname{escapeRate}(C, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeRate_generatedKernel_eq_escapeRate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.20 (Generator union computes meet).**

$$\operatorname{generatedKernel}(C, \operatorname{union}(S, T)) = \operatorname{inf}(\operatorname{generatedKernel}(C, S), \operatorname{generatedKernel}(C, T)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.21 (The generated lattice is finite).**

$$\operatorname{Finite}(\operatorname{GeneratedKernel}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_finite_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.22 (Top is the empty-selection kernel).**

$$\operatorname{top}(\operatorname{GeneratedKernel}(C)) = \operatorname{generatedKernel}(C, \operatorname{empty}()).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.top_eq_generatedKernel_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.23 (Bottom is the full-catalog kernel).**

$$\operatorname{bottom}(\operatorname{GeneratedKernel}(C)) = \operatorname{generatedKernel}(C, \operatorname{fullIndexSet}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.bot_eq_generatedKernel_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.24 (Meet is generator union).**

$$\operatorname{inf}(\operatorname{generatedKernel}(C, S), \operatorname{generatedKernel}(C, T)) = \operatorname{generatedKernel}(C, \operatorname{union}(S, T)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.inf_eq_generatedKernel_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.25 (Meet has the greatest-lower-bound law).**

$$\operatorname{IsGLB}(\operatorname{pair}(P, Q), \operatorname{inf}(P, Q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isGLB_inf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.26 (Internal join has the least-upper-bound law).**

$$\operatorname{IsLUB}(\operatorname{pair}(P, Q), \operatorname{sup}(P, Q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isLUB_sup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Definition 1.27 (Generator step).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratorStep`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.GeneratorStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step inserts one catalog generator into a representative and certifies downward refinement.

**Definition 1.28 (Strict generator step).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.StrictGeneratorStep`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.StrictGeneratorStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A generator step is strict exactly when reverse refinement fails.

**Definition 1.29 (Collapsed addition).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.CollapsedAddition`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.CollapsedAddition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A collapsed addition is a certified generator step whose endpoints are one extensional node.

**Theorem 1.30 (Generator insertion respects extensional equality).**

$$\operatorname{generatedKernel}(C, S) = \operatorname{generatedKernel}(C, T) \Rightarrow \operatorname{generatedKernel}(C, \operatorname{insert}(i, S)) = \operatorname{generatedKernel}(C, \operatorname{insert}(i, T)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatorStep_wellDefined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.31 (Escape is antitone on generator steps).**

$$\operatorname{GeneratorStep}(C, P, Q, i) \Rightarrow \operatorname{escapeAt}(Q) \subseteq \operatorname{escapeAt}(P).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escape_antitone_on_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.32 (Strict refinement exactly means nonempty capture).**

$$\operatorname{GeneratorStep}(C, P, Q, i) \Rightarrow \neg\operatorname{KernelRefines}(P, Q) \iff \operatorname{edgeCapture}(P, Q) \neq \operatorname{empty}().$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strict_kernel_iff_nonempty_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.33 (Strict generator steps have nonempty increments).**

$$\operatorname{StrictGeneratorStep}(C, P, Q, i) \iff \operatorname{GeneratorStep}(C, P, Q, i) \land \operatorname{Nonempty}(\operatorname{edgeCapture}(P, Q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strictGeneratorStep_iff_generatorStep_and_nonempty_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.34 (Collapsed additions capture nothing).**

$$\operatorname{CollapsedAddition}(C, P, i) \Rightarrow \operatorname{edgeCapture}(P, P) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.collapsedAddition_edgeCapture_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate is proved from the extensional quotient and the landed catalog kernel laws.

**Theorem 1.35 (Strict refinement exactly means positive capture count).**

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
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.collapsedAddition_edgeCapture_eq_empty`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCapture`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.edgeCaptureRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeAt_generatedKernel_eq_escapePairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escapeRate_generatedKernel_eq_escapeRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.escape_antitone_on_step`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelRelation`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernelSetoid`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_finite_lattice`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatedKernel_union`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.generatorStep_wellDefined`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.inf_eq_generatedKernel_union`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isGLB_inf`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.isLUB_sup`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.nodesEqB`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.nodesEqB_eq_true_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relation`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relationB`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relationB_eq_true_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.relation_generatedKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strictGeneratorStep_iff_generatorStep_and_nonempty_increment`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strict_kernel_iff_edgeCapture_card_pos`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.strict_kernel_iff_nonempty_increment`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.top_eq_generatedKernel_empty`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/ExactRate](../InformationEscape/ExactRate.md)
