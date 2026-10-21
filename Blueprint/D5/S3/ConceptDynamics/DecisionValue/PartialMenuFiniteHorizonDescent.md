# Finite-Horizon Descent for Partial Menus

## Abstract

Fiberwise partial menus preserve finite-horizon values, tied legal actions, and tagged prefix traces.

A partial menu model assigns each state a finite nonempty set of named legal actions. The model also records a successor, real reward and terminal value, successful outputs and costs, and a tagged failure report with its failure cost. An action outside the menu takes the failure branch; it is never silently added to the menu.

**Theorem 1.1 (Partial-menu value, action, and prefix descent).**

Lean statement: `D5/S3/ConceptDynamics/DecisionValue/PartialMenuFiniteHorizonDescent.partial_menu_finite_horizon_descent`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/PartialMenuFiniteHorizonDescent.partial_menu_finite_horizon_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two models are related by an abstraction. Their legal menus agree on every abstract fiber. Legal successors, rewards, terminal values, successful outputs and costs, and illegal failure reports and costs all factor through that abstraction.

Induction on the remaining horizon compares the finite maxima over the same legal labels. It gives equal Bellman values and exactly the same set of all tied optimal legal labels. A second induction on an arbitrary named action prefix compares the tagged execution records: successful outputs, total cost, failure reports, and the final abstract state agree. An illegal label remains a failure in both runs.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/PartialMenuFiniteHorizonDescent.partial_menu_finite_horizon_descent`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent](FiniteHorizonOptimalActionDescent.md)
- Dependency: [D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization](../DecisionValueScale/FiniteHorizonValueFactorization.md)
