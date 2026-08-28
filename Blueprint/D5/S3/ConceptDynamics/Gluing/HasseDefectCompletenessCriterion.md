# Hasse Completeness and Directional Defects

## Abstract

A local predicate family is Hasse complete exactly when both directional defect sets are empty.

**Theorem 1.1 (Hasse completeness is equivalent to two empty defect sets).**

$$\begin{aligned}\forall X, I: \operatorname{Type}, P: X \to \operatorname{Prop},\\L: I \to X \to \operatorname{Prop},\\(\forall x: X, P(x) \iff (\forall i: I, L(i)(x))) \iff\\\{x: X \mid (\forall i: I, L(i)(x)) \land \neg P(x)\} = \emptyset \land\\\{x: X \mid P(x) \land \neg(\forall i: I, L(i)(x))\} = \emptyset.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/HasseDefectCompletenessCriterion.hasse_complete_iff_positive_negative_defects_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive defect set contains objects satisfying every local predicate but not the global predicate. The negative defect set contains globally valid objects rejected by at least one local predicate.

Pointwise global-local equivalence excludes both sets. Conversely, their separate emptiness supplies the two implications of the equivalence for every object.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/HasseDefectCompletenessCriterion.hasse_complete_iff_positive_negative_defects_empty`
