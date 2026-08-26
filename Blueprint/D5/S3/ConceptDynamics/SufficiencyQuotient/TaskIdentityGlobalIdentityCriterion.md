# Task Identity and Global Identity

## Abstract

The target-profile quotient is the operational identity, and it becomes global identity exactly for a jointly faithful target family.

**Theorem 1.1 (Task identity equals global identity exactly under joint faithfulness).**

$$\left(\forall I \in \operatorname{Type}\left(\right), X \in \operatorname{Type}\left(\right), Y \in I \to \operatorname{Type}\left(\right), K \in \left(\forall i \in I,\; X \to Y\left(i\right)\right),\; \left(\forall x \in X, y \in X,\; \operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(K\right)\right)\left(x\right) = \operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(K\right)\right)\left(y\right) \Leftrightarrow \left(\forall i \in I,\; K\left(i\right)\left(x\right) = K\left(i\right)\left(y\right)\right)\right) \land \left(\left(\operatorname{Injective}\left(\operatorname{jointReadout}\left(K\right)\right) \Leftrightarrow \operatorname{ker}\left(\operatorname{jointReadout}\left(K\right)\right) = \operatorname{Eq}\left(X\right)\right) \land \left(\operatorname{Injective}\left(\operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(K\right)\right)\right) \Leftrightarrow \operatorname{Injective}\left(\operatorname{jointReadout}\left(K\right)\right)\right)\right)\right) \land \left(\exists q \in \left(\forall j \in Unit,\; Bool \to Unit\right),\; \exists x \in Bool, y \in Bool,\; x \ne y \land \left(\left(\forall j \in Unit,\; q\left(j\right)\left(x\right) = q\left(j\right)\left(y\right)\right) \land \operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(q\right)\right)\left(x\right) = \operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(q\right)\right)\left(y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SufficiencyQuotient/TaskIdentityGlobalIdentityCriterion.task_identity_global_identity_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target family is assembled by the canonical dependent joint readout. Its kernel quotient is exposed through the canonical class map, so two states have the same task identity exactly when every target returns the same value on them.

The joint readout is injective exactly when its kernel is equality. The same condition makes the quotient class map injective, which is the precise sense in which task identity then agrees with global identity.

A constant target family on Bool gives two distinct states with equal target values and equal quotient classes, making the separation clause substantive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SufficiencyQuotient/TaskIdentityGlobalIdentityCriterion.task_identity_global_identity_criterion`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
