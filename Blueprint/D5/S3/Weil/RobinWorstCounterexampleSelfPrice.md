# Robin Worst Counterexample Self-Price

## Abstract

A negative Robin-margin minimizer on an admissible set is optimal at its own logarithmic price.

**Theorem 1.1 (A worst strict counterexample is self-priced optimal).**

$$\forall A \in Set\left(\mathbb{N}\right),\; \left(\left(\forall n \in \mathbb{N},\; n \in A \Rightarrow 5041 \le n\right) \land \left(\exists n \in \mathbb{N},\; n \in A \land robinLogMargin\left(n\right) < 0\right)\right) \Rightarrow \left(\exists nstar \in \mathbb{N},\; nstar \in A \land \left(robinLogMargin\left(nstar\right) < 0 \land \left(\left(\forall n \in \mathbb{N},\; n \in A \Rightarrow robinLogMargin\left(nstar\right) \le robinLogMargin\left(n\right)\right) \land \left(\forall n \in \mathbb{N},\; n \in A \Rightarrow goldenResourceObjective\left(\frac{1}{log\left(nstar\right) \cdot log\left(log\left(nstar\right)\right)}, n\right) \le goldenResourceObjective\left(\frac{1}{log\left(nstar\right) \cdot log\left(log\left(nstar\right)\right)}, nstar\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/RobinWorstCounterexampleSelfPrice.robin_worst_counterexample_self_price` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vanishing lower limit of the logarithmic Robin margin makes every sublevel below a strict negative value finite. A minimum on the admissible set therefore exists and remains strictly negative.

For the minimizing integer, the derivative of log(log E) at E = log n is 1 divided by E log E. Strict concavity gives the supporting tangent inequality, and the margin identity converts it into the global maximum of the resource objective W minus lambda E.

## References

- Truth anchor: `D5/S3/Weil/RobinWorstCounterexampleSelfPrice.robin_worst_counterexample_self_price`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../Arith/GoldenResourceOptimalInteger.md)
- Dependency: [D5/S3/Weil/GronwallLowerEnvelope](GronwallLowerEnvelope.md)
