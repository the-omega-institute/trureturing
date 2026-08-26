# Coordinate-Deletion Robustness

## Abstract

One more separating coordinate than the deletion budget preserves joint faithfulness.

**Theorem 1.1 (Redundant separation survives bounded coordinate deletion).**

$$\begin{aligned}\forall I, X: \operatorname{Type}, O: I \to \operatorname{Type},\\q: \forall i: I, X \to O(i), f \in \mathbb{N},\\(\forall x, y: X, x \neq y \Rightarrow (\exists S: \operatorname{Finset}\left(I\right), \operatorname{card}\left(S\right) = f + 1 \land \forall i: S, \operatorname{q}\left(i, x\right) \neq \operatorname{q}\left(i, y\right))) \Rightarrow\\\forall D: \operatorname{Finset}\left(I\right), \operatorname{card}\left(D\right) \leq f \Rightarrow\\\operatorname{Injective}\left(\operatorname{jointReadout}\left(\operatorname{restrict}\left(q, \{i: I \mid \neg(i \in D)\}\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/CoordinateDeletionRobustness.coordinate_deletion_robustness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every distinct pair of states, the premise supplies a finite set of exactly f + 1 coordinates whose readouts separate that pair. This witness form states the source's at-least condition without requiring decidable equality on any output carrier.

A deleted coordinate set of cardinality at most f cannot contain the entire separating witness. Evaluating equal surviving joint readouts at a witness outside the deleted set contradicts its separation property.

The conclusion uses the existing dependent jointReadout on the subtype of coordinates outside the deleted set, so completeness is injectivity of the canonical surviving observation family.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/CoordinateDeletionRobustness.coordinate_deletion_robustness`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](JointFaithfulnessLeibnizCriterion.md)
