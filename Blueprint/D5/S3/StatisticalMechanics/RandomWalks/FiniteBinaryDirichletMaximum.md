# A maximum principle for two weighted successors

## Abstract

An attained absolute maximum propagates along every positive-weight transition to the zero boundary.

**Theorem 1.1 (Zero boundary and exit paths force a zero maximum).**

$$\forall S \in \operatorname{Type},\; \forall f \in S \to \mathbb{R},\; \forall M \in \mathbb{R},\; \forall boundary \in S \to \operatorname{Prop},\; \forall l \in S \to S,\; \forall r \in S \to S,\; \forall a \in S \to \mathbb{R},\; \forall b \in S \to \mathbb{R},\; (\forall s \in S,\; \left|f\left(s\right)\right| \le M) \Rightarrow ((\exists s \in S,\; \left|f\left(s\right)\right| = M) \Rightarrow ((\forall s \in S,\; (boundary\left(s\right)) \Rightarrow (f\left(s\right) = 0)) \Rightarrow ((\forall s \in S,\; (\neg (boundary\left(s\right))) \Rightarrow (0 \le a\left(s\right) \land (0 \le b\left(s\right) \land (a\left(s\right) + b\left(s\right) = 1)))) \Rightarrow ((\forall s \in S,\; (\neg (boundary\left(s\right))) \Rightarrow (f\left(s\right) = a\left(s\right) \cdot f\left(l\left(s\right)\right) + b\left(s\right) \cdot f\left(r\left(s\right)\right))) \Rightarrow ((\forall s \in S,\; \exists t \in S,\; boundary\left(t\right) \land (\operatorname{Relation}.\operatorname{ReflTransGen}\left(\lambda s:S \mapsto \lambda t:S \mapsto \left(\neg (boundary\left(s\right))\right) \land (\left(0 < a\left(s\right) \land (l\left(s\right) = t)\right) \lor (0 < b\left(s\right) \land (r\left(s\right) = t))), s, t\right))) \Rightarrow (M = 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/RandomWalks/FiniteBinaryDirichletMaximum.maximum_zero_of_two_successor_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real-valued harmonic function has a uniform attained absolute maximum M. At every nonboundary state its two outgoing weights are nonnegative and sum to one. A successor with positive weight must have the same absolute value as a maximizing state. Propagating this equality along a finite positive-weight path to the zero boundary gives M = 0. The state type need not be finite: an attained uniform bound is sufficient.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/FiniteBinaryDirichletMaximum.maximum_zero_of_two_successor_exit`
