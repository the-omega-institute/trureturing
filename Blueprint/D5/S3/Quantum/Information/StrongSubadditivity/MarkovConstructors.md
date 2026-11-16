# Physical quantum Markov constructors

## Abstract

All states use the canonical finite density-state interface on A times (B times C). Conditional mutual information is the ordinary entropy expression evaluated on the four actual marginals. Product and orthogonal pointer constructions have zero conditional mutual information for all ranks, including zero mixture weights.

**Theorem 1.1 (The four actual marginal entropies).**

Lean statement: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_eq_four_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_eq_four_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary qcmi of the canonical state converted to MState equals the entropy of its actual AB marginal plus the entropy of its actual BC marginal minus the entropy of its actual B marginal and the entropy of the state itself.

**Theorem 1.2 (A product across A and BC).**

Lean statement: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every density state a on A and every density state omega on B times C, the physical product a tensor omega has ordinary conditional mutual information zero. Product entropy additivity applies without a rank condition.

**Theorem 1.3 (A product across AB and C).**

Lean statement: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every density state P on A times B and every density state gamma on C, relabeling P tensor gamma onto A times (B times C) gives ordinary conditional mutual information zero.

**Definition 1.4 (An orthogonal pointer state).**

Lean statement: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.classicalMarkovState`

*Formalization.* `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.classicalMarkovState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A probability vector on B and normalized conditional states alpha(j) on A and gamma(j) on C define the mixture of alpha(j) tensor the computational pointer j tensor gamma(j). Zero weights do not require division.

**Theorem 1.5 (Conditional independence in every pointer block).**

Lean statement: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_classicalMarkovState`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_classicalMarkovState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orthogonal pointer mixture has ordinary conditional mutual information zero. Each of its four actual marginal entropies is evaluated using product additivity and the orthogonal record entropy formula; the classical entropy and both conditional entropy sums cancel.

## References

- Truth anchor: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.classicalMarkovState`
- Truth anchor: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_classicalMarkovState`
- Truth anchor: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_eq_four_marginals`
- Truth anchor: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_left`
- Truth anchor: `D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_right`
- Dependency: [D5/S3/Quantum/Information/MarginalCalculus](../MarginalCalculus.md)
