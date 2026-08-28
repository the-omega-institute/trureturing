# No Guaranteed Remedy Outside the Winning Region

## Abstract

Outside every finite winning stage, no bounded strategy guarantees a remedy.

**Theorem 1.1 (Outside the winning region there is no guaranteed remedy).**

$$\begin{gathered}\forall X: \operatorname{Type},\\{}S: \operatorname{ControlSystem}(X), G: \operatorname{Set}(X), x: X,\\{}\neg \exists n \in \mathbb{N}, x \in \operatorname{winningRegion}(S, G, n) \Rightarrow\\{}(\neg \exists n \in \mathbb{N}, \operatorname{BoundedReachStrategy}(S, G, n, x)) \land\\{}(\forall xPrime: X, xPrime \in G \Rightarrow \neg \exists n \in \mathbb{N}, \operatorname{BoundedReachStrategy}(S, G, n, x)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/NoGuaranteedRemedyOutsideWinningRegion.no_guaranteed_remedy_outside_winning_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The control system, goal set, actual state, finite winning stages, and bounded reach strategies are the canonical control-family objects.

If the actual state belongs to no finite winning stage, the finite-horizon reachability equivalence excludes every bounded strategy that guarantees reaching the goal.

The second public clause quantifies an exhibited counterfactual state in the same goal. Its existence does not produce a strategy from the actual state.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/NoGuaranteedRemedyOutsideWinningRegion.no_guaranteed_remedy_outside_winning_region`
- Dependency: [D5/S3/ConceptDynamics/Control/FiniteHorizonReachability](FiniteHorizonReachability.md)
