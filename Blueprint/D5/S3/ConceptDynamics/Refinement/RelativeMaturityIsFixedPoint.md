# Relative Maturity as a Fixed-Point Criterion

## Abstract

A concept is mature relative to a question family exactly when every question in the family already factors through it, and this maturity is not absolute.

**Theorem 1.1 (Relative maturity is exactly family-wide answerability).**

$$\forall I \in Type, X \in Type, C \in Type, V \in Type, qC \in X \to C, questions \in I \to \left(X \to V\right),\; \operatorname{MatureFor}\left(qC, questions\right) \Leftrightarrow \left(\forall n \in I,\; \operatorname{Refines}\left(questions\left(n\right), qC\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/RelativeMaturityIsFixedPoint.mature_iff_all_questions_answerable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept is mature for a family precisely when every question readout in that family factors through the concept. Equivalently, adjoining any one of those questions to the concept creates no distinction that the concept itself cannot already recover.

For the forward direction, project a joint completion to its question coordinate and compose that projection with the maturity collapse. Conversely, the identity factorization of the concept together with the assumed factorization of each question invokes the universal property of the concept join.

**Theorem 1.2 (Maturity depends on the question family).**

$$\exists qC \in Bool \times Bool \to Bool, questions \in Unit \to \left(Bool \times Bool \to Bool\right), otherQuestions \in Unit \to \left(Bool \times Bool \to Bool\right),\; \operatorname{MatureFor}\left(qC, questions\right) \land \left(\neg \operatorname{MatureFor}\left(qC, otherQuestions\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/RelativeMaturityIsFixedPoint.relative_maturity_is_not_absolute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the first Boolean coordinate as the concept. The constant Unit-indexed family that asks for that same first coordinate factors through the concept by the identity map, so the concept is mature for this family.

The corresponding family that asks for the second coordinate does not factor through the first: the states (false, false) and (false, true) have the same first coordinate but different second coordinates. Thus one fixed concept is mature for one family and not mature for another.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/RelativeMaturityIsFixedPoint.mature_iff_all_questions_answerable`
- Truth anchor: `D5/S3/ConceptDynamics/Refinement/RelativeMaturityIsFixedPoint.relative_maturity_is_not_absolute`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
