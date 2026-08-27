# Optimal-Fiber Alignment Underdetermination

## Abstract

Unequal principal values within one proxy-optimal fiber preclude a principal-best selection guarantee.

**Theorem 1.1 (A proxy-optimal tie precludes a principal-best guarantee).**

$$\forall Z \in Type, agentObjective \in Z \to \mathbb{R}, principalObjective \in Z \to \mathbb{R}, first \in Z, second \in Z,\; \left(agentObjective\left(first\right) = agentObjective\left(second\right) \land \left(\left(\forall candidate \in Z,\; agentObjective\left(candidate\right) \le agentObjective\left(first\right)\right) \land principalObjective\left(first\right) \ne principalObjective\left(second\right)\right)\right) \Rightarrow \left(\neg \left(\forall selected \in Z,\; \left(\forall candidate \in Z,\; agentObjective\left(candidate\right) \le agentObjective\left(selected\right)\right) \Rightarrow \left(\forall alternative \in Z,\; \left(\forall candidate \in Z,\; agentObjective\left(candidate\right) \le agentObjective\left(alternative\right)\right) \Rightarrow principalObjective\left(alternative\right) \le principalObjective\left(selected\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/OptimalFiberAlignmentUnderdetermination.proxy_optimal_tie_precludes_principal_guarantee` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two objectives are real-valued on the same feasible carrier. The first state is globally proxy-optimal, and the proxy tie makes the second state globally proxy-optimal as well.

If every proxy-maximizing selection were principal-best among all proxy maximizers, selecting each tied state in turn would force the two principal values to be equal, contradicting the source witness.

The source's subsequent three-part alignment prescription uses qualitative terms without in-scope predicates and is commentary outside the named formal theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/OptimalFiberAlignmentUnderdetermination.proxy_optimal_tie_precludes_principal_guarantee`
