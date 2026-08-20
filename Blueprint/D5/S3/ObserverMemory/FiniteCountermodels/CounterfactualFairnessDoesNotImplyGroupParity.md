# Counterfactual Fairness Does Not Imply Group Parity

## Abstract

Protected-attribute invariance can coexist with unequal observed group decision rates.

**Theorem 1.1 (Counterfactual fairness need not imply group parity).**

$$\begin{gathered}P=\left\{(0, 0), (1, 1)\right\},\\\forall g, p, r, I(g(p, r))=(g, r) \land J(I(g(p, r)))=J((p, r)),\\\forall p, r, (p, r) \in P \Rightarrow r=p,\\G_{0} \neq \emptyset \land G_{1} \neq \emptyset,\\\rho_{0}=0 \land \rho_{1}=1 \land \rho_{0} \neq \rho_{1}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/CounterfactualFairnessDoesNotImplyGroupParity.counterfactual_fairness_does_not_imply_group_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The decision reads only qualification r. Every protected intervention replaces p by a chosen Boolean value g while retaining r, so the decision is pointwise invariant for every state and intervention value.

The explicit two-point population is supported on r=p. Both protected groups are nonempty, making the conditional counting denominators one. The group with p=0 has decision rate zero and the group with p=1 has decision rate one.

The rate is derived from finite member and positive-member counts rather than installed as a constant. Repository and pinned-library searches found no existing theorem joining counterfactual invariance to these group-rate clauses.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/CounterfactualFairnessDoesNotImplyGroupParity.counterfactual_fairness_does_not_imply_group_parity`
