# OP5 Pareto Stop Equivalences Are Refuted

## Abstract

A complete sourced two-action model refutes both OP5 Pareto linear-extension stop equivalences.

**Theorem 1.1 (Dominance direction reverses the proposed stop characterizations).**

$$\left(\operatorname{Nonempty}\left(\operatorname{feasible}\left(\right)\right) \land \left(\operatorname{feasible}\left(\operatorname{decision}\left(\operatorname{commitment}\left(\right)\right)\right) = \operatorname{feasible}\left(\right) \land \left(\operatorname{current}\left(\operatorname{decision}\left(\operatorname{commitment}\left(\right)\right)\right) = \operatorname{some}\left(true\right) \land \left(\left(\forall action \in \operatorname{Bool}\left(\right),\; action \in \operatorname{feasible}\left(\right) \Rightarrow \left(action \in \operatorname{admissibleTarget}\left(\operatorname{goal}\left(\operatorname{paretoOrientation}\left(\right)\right)\right) \land \operatorname{inScope}\left(\operatorname{scope}\left(\operatorname{paretoOrientation}\left(\right)\right), action\right)\right)\right) \land \left(\operatorname{ParetoMaximalIn}\left(\operatorname{value}\left(\right), \operatorname{feasible}\left(\right), true\right) \land \left(\operatorname{ParetoGreatestIn}\left(\operatorname{value}\left(\right), \operatorname{feasible}\left(\right), true\right) \land \operatorname{Nonempty}\left(\operatorname{LinearExtension}\left(\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\neg \left(\operatorname{ParetoMaximalIn}\left(\operatorname{value}\left(\right), \operatorname{feasible}\left(\right), true\right) \Leftrightarrow \left(\exists L \in \operatorname{LinearExtension}\left(\right),\; \operatorname{OrientedStop}\left(\operatorname{admissibleTarget}\left(\right), \operatorname{InFiniteNarrowedScope}\left(\operatorname{inScope}\left(\right)\right), \operatorname{orientation}\left(L\right), \operatorname{commitment}\left(\right)\right)\right)\right)\right) \land \left(\neg \left(\left(\forall L \in \operatorname{LinearExtension}\left(\right),\; \operatorname{OrientedStop}\left(\operatorname{admissibleTarget}\left(\right), \operatorname{InFiniteNarrowedScope}\left(\operatorname{inScope}\left(\right)\right), \operatorname{orientation}\left(L\right), \operatorname{commitment}\left(\right)\right)\right) \Leftrightarrow \operatorname{ParetoGreatestIn}\left(\operatorname{value}\left(\right), \operatorname{feasible}\left(\right), true\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoLinearExtensionStopRefutation.op5_pareto_stop_linear_extension_equivalences_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The feasible carrier is Bool and the current action is true. True has strictly better values in all three benefit coordinates and strictly lower values in both cost coordinates, so it is both Pareto-maximal and Pareto-greatest under the frozen dominance convention.

Each LinearExtension value contains a complete linear order on the explicit finite Pareto quotient, a proof that it extends QuotientParetoWeak, and a full OrientationSpec. The latter preserves goal, source, and version and records the narrowed scope as the original scope paired with the feasible Finset.

A Szpilrajn extension witnesses that the extension family is nonempty. Every member places the dominating true class before the false class. OrientedStop rejects strict successors of current, hence no member stops at true and both displayed equivalences fail.

The displayed certificate includes every OP5 side condition: nonempty feasibility, the sealed feasible/current fields, admissibility and original-scope membership, maximality, greatestness, and extension nonemptiness. Repository, pinned-Mathlib, and third-party searches found no existing theorem with this sourced-stop statement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoLinearExtensionStopRefutation.op5_pareto_stop_linear_extension_equivalences_refuted`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/AdjudicationStopTargetCorrectness](AdjudicationStopTargetCorrectness.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/QuotientParetoWeakOrder](QuotientParetoWeakOrder.md)
