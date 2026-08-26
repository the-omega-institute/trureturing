# Joint Resource Safety Criterion

## Abstract

Jointly attainable local extraction caps guarantee resource safety exactly when their total fits the stock-plus-recovery budget.

**Theorem 1.1 (Jointly attainable caps characterize resource safety).**

$$\left(\forall Agent \in Type, s \in Real, smin \in Real, g \in Real \to Real, c \in Agent \to Real, Feasible \in (Agent \to Real) \to Prop,\; \left(\left(\operatorname{Fintype}\left(Agent\right) \land Feasible\left(c\right)\right) \land \left(\forall a \in Agent \to Real,\; Feasible\left(a\right) \Rightarrow \left(\forall i \in Agent,\; 0 \le a\left(i\right) \land a\left(i\right) \le c\left(i\right)\right)\right)\right) \Rightarrow \left(\left(\forall a \in Agent \to Real,\; Feasible\left(a\right) \Rightarrow smin \le s + g\left(s\right) - \operatorname{sum}\left(a\right)\right) \Leftrightarrow \operatorname{sum}\left(c\right) \le s + g\left(s\right) - smin\right)\right) \land \left(\exists s \in Real, smin \in Real, g \in Real \to Real, c \in \operatorname{Fin}\left(2\right) \to Real, a \in \operatorname{Fin}\left(2\right) \to Real,\; \left(\left(\left(\left(\left(\left(s = 1 \land smin = 0\right) \land g = \operatorname{const}\left(0\right)\right) \land c = \operatorname{const}\left(\frac{3}{4}\right)\right) \land a = c\right) \land \left(\forall j \in \operatorname{Fin}\left(2\right),\; 0 \le a\left(j\right) \land a\left(j\right) \le c\left(j\right)\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(2\right),\; smin \le s + g\left(s\right) - a\left(j\right)\right)\right) \land s + g\left(s\right) - \operatorname{sum}\left(a\right) < smin\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TargetRisk/JointResourceSafetyCriterion.jointly_attainable_caps_characterize_resource_safety` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A feasible extraction is constructed from a finite family of agents, a current stock, its recovery rule, and local extraction caps. The cap vector itself is explicitly required to be feasible.

If every feasible extraction is nonnegative and bounded pointwise by the caps, then all feasible next-period stocks meet the minimum exactly when the sum of the caps fits the recoverable budget.

The same two-agent cap and extraction vectors witness the contrast: each three-quarter extraction alone leaves nonnegative stock, while their joint extraction drives the next stock below zero.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TargetRisk/JointResourceSafetyCriterion.jointly_attainable_caps_characterize_resource_safety`
