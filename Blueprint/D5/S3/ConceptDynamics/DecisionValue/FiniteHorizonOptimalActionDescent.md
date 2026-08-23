# Finite-Horizon Optimal-Action Descent

## Abstract

Exact causal abstraction preserves every finite-horizon optimal-action set.

**Theorem 1.1 (Optimal action concept descends).**

$$\begin{gathered}[\operatorname{Fintype}(U)], U \neq \emptyset,\\{}(\forall u, x, C(F_{u}(x)) = G_{u}(C(x))) \land\\{}(\forall x, u, r(x, u) = \overline{r}(C(x), u)) \land\\{}(\forall x, q(x) = \overline{q}(C(x)))\longrightarrow\\{}\forall n, x, \operatorname{argmax}_{u\in U} [r(x, u) + V_{n}(F_{u}(x))] =\\{}\operatorname{argmax}_{u\in U} [\overline{r}(C(x), u) + \overline{V_{n}}(G_{u}(C(x)))].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent.finite_horizon_optimal_actions_descend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common action carrier is finite and nonempty. Micro transitions commute with the abstraction, while both stage rewards and terminal values factor through the abstract state.

Induction through the finite maximum first identifies the micro Bellman value with the macro value at C(x). Substitution in each action score then identifies the two maximizing-action sets pointwise, so the optimal decision depends only on C(x).

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent.finite_horizon_optimal_actions_descend`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
