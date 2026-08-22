# Zero Conditional Logical Impurity

## Abstract

Zero conditional pair impurity characterizes fiberwise target constancy.

**Definition 1.1 (Concept fiber mass).**

Lean statement: `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.conceptFiberMass`

*Formalization.* `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.conceptFiberMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass of a concept fiber is constructed by summing the source probability mass over states with the selected concept coordinate.

**Definition 1.2 (Pair disagreement mass).**

Lean statement: `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.pairDisagreementMass`

*Formalization.* `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.pairDisagreementMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair cost sums the mass of ordered state pairs in one concept fiber whose target readouts differ.

**Definition 1.3 (Conditional logical impurity).**

Lean statement: `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.conditionalLogicalImpurity`

*Formalization.* `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.conditionalLogicalImpurity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each fiber pair-disagreement mass is normalized by its fiber mass, and these contributions are summed over concept coordinates.

**Theorem 1.4 (Zero impurity exactly characterizes support-level constancy).**

$$\begin{gathered}\forall X, B, A: \operatorname{Type},\\{}\mu: \operatorname{PMF}(X), C: X \to B, T: X \to A,\\{}\operatorname{conditionalLogicalImpurity}(\mu, C, T) = 0 \iff\\{}\forall b, \operatorname{conceptFiberMass}(\mu, C, b) \neq 0 \Rightarrow \exists t,\\{}\forall x, (C(x) = b \land \mu(x) \neq 0) \Rightarrow T(x) = t.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.zero_impurity_iff_fiber_ae_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Almost-everywhere constancy is stated directly for the discrete probability law: every supported state in a positive-mass concept fiber has one common target value.

The forward direction selects a supported state in each positive fiber and uses zero pair cost against every other supported state. The reverse direction makes every disagreement term vanish, including on zero-mass fibers.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.conceptFiberMass`
- Truth anchor: `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.conditionalLogicalImpurity`
- Truth anchor: `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.pairDisagreementMass`
- Truth anchor: `D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.zero_impurity_iff_fiber_ae_constant`
