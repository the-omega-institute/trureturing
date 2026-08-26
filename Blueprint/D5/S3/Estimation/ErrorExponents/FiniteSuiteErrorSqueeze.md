# Finite-Suite Error Squeeze

## Abstract

Optimal equal-prior error for a finite independent suite is squeezed by its Bhattacharyya evidence budget.

**Theorem 1.1 (Finite-suite optimal error obeys the affinity squeeze).**

$$\begin{aligned}\forall Index, Outcome: \operatorname{Type},\\{}[\operatorname{Fintype}(Index)], [\operatorname{DecidableEq}(Index)],\\{}[\operatorname{Fintype}(Outcome)],\\p, q: Index \to \left(Outcome \to \mathbb{R}\right),\\(\forall i, (\forall a, 0 \leq \operatorname{p}(i, a)) \land \sum_{a} \operatorname{p}(i, a) = 1) \land\\(\forall i, (\forall a, 0 \leq \operatorname{q}(i, a)) \land \sum_{a} \operatorname{q}(i, a) = 1) \land\\(\forall i, 0 < \operatorname{bhattacharyya}(p_{i}, q_{i})) \Rightarrow\\\frac{1-\sqrt{1-\operatorname{exp}(-2\operatorname{finiteSuiteBhattacharyyaBudget}(p, q))}}{2} \leq \operatorname{finiteSuiteOptimalError}(p, q) \land\\\operatorname{finiteSuiteOptimalError}(p, q) \leq \frac{\operatorname{exp}(-\operatorname{finiteSuiteBhattacharyyaBudget}(p, q))}{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteErrorSqueeze.finite_suite_error_squeeze` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The suite law is the canonical windowLaw product of its coordinate laws. The equal-prior error is minimized over all decision events on the finite outcome-vector space, so the public quantity is an operational testing risk rather than a restatement of either bound.

The budget is the negative sum of the logarithms of the coordinate Bhattacharyya affinities. Exact affinity multiplicativity turns its exponential back into the joint-law affinity, while the sharp lower and upper estimates follow from the total-variation comparisons.

Every coordinate affinity is assumed strictly positive. This is the exact restriction needed for a finite real logarithmic budget: a zero affinity corresponds to infinite evidence, which cannot be represented by Lean's totalized real logarithm.

## References

- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteErrorSqueeze.finite_suite_error_squeeze`
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger](../../Entropy/NamingWindow/GreenClassWindowHellinger.md)
- Dependency: [D5/S3/Estimation/LeCamTight](../LeCamTight.md)
