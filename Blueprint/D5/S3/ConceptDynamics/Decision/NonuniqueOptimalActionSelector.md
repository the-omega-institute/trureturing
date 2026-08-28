# Nonunique Optimal Actions and Ordered Selection

## Abstract

A determined optimizer set can remain non-singleton until an ordered tie-breaker is added.

**Theorem 1.1 (A determined optimum need not determine one policy).**

$$\exists K \in Bool \to \operatorname{PMF}\left(Unit\right), ell \in Bool \to \left(Unit \to \mathbb{R}\right),\; \operatorname{let} R: Bool \to \left(Bool \to \mathbb{R}\right), \forall x: Bool, a: Bool, R\left(x, a\right) := \operatorname{integral}\left(\operatorname{toMeasure}\left(K\left(x\right)\right), ell\left(a\right)\right); \operatorname{let} Opt: Bool \to \operatorname{Set}\left(Bool\right), \forall x: Bool, Opt\left(x\right) := \left\{a: Bool \mid \forall b \in Bool,\; R\left(x, a\right) \le R\left(x, b\right)\right\}; \operatorname{let} concept: Bool \to Unit, \forall x: Bool, concept\left(x\right) := unit; \operatorname{let} s: Bool \to Bool, \forall x: Bool, s\left(x\right) := false; \operatorname{Refines}\left(Opt, concept\right) \land \left(\left(\forall x \in Bool,\; \operatorname{ncard}\left(Opt\left(x\right)\right) = 2\right) \land \left(\left(\forall x \in Bool,\; s\left(x\right) \in Opt\left(x\right)\right) \land \left(\left(\forall x \in Bool, a \in Bool,\; a \in Opt\left(x\right) \Rightarrow s\left(x\right) \le a\right) \land \left(\left(\forall x \in Bool, u \in Bool,\; \left(u \in Opt\left(x\right) \land \left(\forall a \in Bool,\; a \in Opt\left(x\right) \Rightarrow u \le a\right)\right) \Rightarrow u = s\left(x\right)\right) \land \left(\forall x \in Bool,\; \exists a \in Bool,\; a \in Opt\left(x\right) \land a \ne s\left(x\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/NonuniqueOptimalActionSelector.determined_optimal_set_can_be_nonunique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prediction is a constant PMF on Unit and every Boolean action has zero loss. Expected loss and the optimizer readout are constructed from that same prediction and loss, so the optimizer is determined but contains both actions.

The fixed Boolean order selects false as the unique least optimum. The true action remains optimal, making explicit that single-valuedness belongs to the added order rather than to the original risk profile.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/NonuniqueOptimalActionSelector.determined_optimal_set_can_be_nonunique`
- Dependency: [D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency](PredictionDecisionSufficiency.md)
