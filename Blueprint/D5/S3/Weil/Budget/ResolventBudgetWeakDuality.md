# Resolvent Budget Weak Duality

## Abstract

Local matching and resolvent feasibility give weak primal-dual order.

**Theorem 1.1 (Feasible primal floors lie below feasible dual values).**

$$\begin{aligned}\forall Test: \operatorname{Type}, fourierReading: Test \to \left(\mathbb{R} \to \mathbb{R}\right),\\atZero: Test \to \mathbb{R}, weilPairing: Test \to \mathbb{R},\\mu: \operatorname{Measure}(\mathbb{R}), phi: Test, a: \mathbb{R}, lambda: \mathbb{R}, theta: \mathbb{R}, C: \mathbb{R},\\0 \le lambda \land \left(0 \le theta \land \left(\operatorname{Integrable}(xi: \mathbb{R} \mapsto fourierReading(phi)(xi), mu) \land \left(\operatorname{Integrable}(xi: \mathbb{R} \mapsto \frac{1}{xi^{2} + a^{2}}, mu) \land \left(weilPairing(phi) = lambda \cdot atZero(phi) + \operatorname{integral}(mu, xi: \mathbb{R} \mapsto fourierReading(phi)(xi)) \land \left(\left(\forall xi \in \mathbb{R},\; 0 \le fourierReading(phi)(xi) + theta \cdot \frac{1}{xi^{2} + a^{2}}\right) \land \left(1 \le atZero(phi) + \frac{theta}{2 \cdot a} \land \frac{lambda}{2 \cdot a} + \operatorname{integral}(mu, xi: \mathbb{R} \mapsto \frac{1}{xi^{2} + a^{2}}) \le C\right)\right)\right)\right)\right)\right) \Rightarrow\\lambda \le weilPairing(phi) + theta \cdot C.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ResolventBudgetWeakDuality.resolvent_budget_weak_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public carrier is a positive real-line measure. Fourier reading, evaluation at zero, and local source pairing are supplied on one test carrier; the pairing identity states their local match.

Integrability makes both signed integrals honest. Pointwise Fourier majorization integrates against the positive measure, while nonnegative dual pressure scales the primal budget inequality.

The floor constraint then combines the two estimates into the displayed weak-duality bound.

## References

- Truth anchor: `D5/S3/Weil/Budget/ResolventBudgetWeakDuality.resolvent_budget_weak_duality`
