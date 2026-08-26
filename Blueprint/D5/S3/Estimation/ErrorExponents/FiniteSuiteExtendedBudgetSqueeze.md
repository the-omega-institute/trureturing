# Finite-Suite Extended-Budget Error Squeeze

## Abstract

Optimal equal-prior error for a finite independent suite is squeezed by an extended Bhattacharyya budget, including zero affinity.

**Theorem 1.1 (Finite-suite error squeeze includes zero affinity).**

$$\begin{aligned}\forall Index, Outcome: \operatorname{Type},\\{}[\operatorname{Fintype}(Index)], [\operatorname{DecidableEq}(Index)],\\{}[\operatorname{Fintype}(Outcome)],\\p, q: Index \to \left(Outcome \to \mathbb{R}\right),\\(\forall i, (\forall a, 0 \leq \operatorname{p}(i, a)) \land \sum_{a} \operatorname{p}(i, a) = 1) \land\\(\forall i, (\forall a, 0 \leq \operatorname{q}(i, a)) \land \sum_{a} \operatorname{q}(i, a) = 1) \Rightarrow\\\frac{1-\sqrt{1-\operatorname{bhattacharyyaBudgetDecay}(\operatorname{finiteSuiteExtendedBhattacharyyaBudget}(p, q))^{{2}}}}{2} \leq \operatorname{finiteSuiteOptimalError}(p, q) \land\\\operatorname{finiteSuiteOptimalError}(p, q) \leq \frac{\operatorname{bhattacharyyaBudgetDecay}(\operatorname{finiteSuiteExtendedBhattacharyyaBudget}(p, q))}{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteSuiteExtendedBudgetSqueeze.finite_suite_error_squeeze_extended` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The suite law and optimal equal-prior error are the frozen windowLaw product and finiteSuiteOptimalError, so the tested quantity remains the operational minimum over all finite decision events.

The extended budget is the negative extended logarithm of the joint Bhattacharyya affinity. Its zero-affinity value is infinity, and bhattacharyyaBudgetDecay maps that endpoint to zero while agreeing with the ordinary exponential of the negative finite budget.

Consequently no positivity premise is needed. At zero affinity both displayed bounds reduce to zero, forcing the optimal error itself to be zero.

## References

- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteSuiteExtendedBudgetSqueeze.finite_suite_error_squeeze_extended`
- Dependency: [D5/S3/Estimation/ErrorExponents/FiniteSuiteErrorSqueeze](FiniteSuiteErrorSqueeze.md)
