# Existence-Notion Separation

## Abstract

Formability, proof, construction, model existence, and realization are distinct predicates.

**Definition 1.1 (Model existence).**

Lean statement: `D5/S3/ConceptDynamics/ExistenceNotionSeparation.HasModel`

*Formalization.* `D5/S3/ConceptDynamics/ExistenceNotionSeparation.HasModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A model exists exactly when the externally supplied model predicate has a witness.

**Definition 1.2 (Realization).**

Lean statement: `D5/S3/ConceptDynamics/ExistenceNotionSeparation.Realized`

*Formalization.* `D5/S3/ConceptDynamics/ExistenceNotionSeparation.Realized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Realization is an externally supplied relation between a model and a constructed object.

**Theorem 1.3 (Mathematical existence notions separate).**

$$\begin{aligned}&(\exists P: Prop, \neg P) \land\\&(\exists X: Type, IsEmpty(X)) \land\\&(\forall X: Type, X \to Nonempty(X)) \land\\&(\exists M: Type, q: M \to Prop, HasModel(q)) \land\\&(\exists M: Type, q: M \to Prop, \neg HasModel(q)) \land\\&(\exists M, X: Type, m: M, x: X, R: M \to \left(X \to Prop\right), \neg Realized(R, m, x)) \land\\&(\exists M, X: Type, m: M, x: X, R: M \to \left(X \to Prop\right), Realized(R, m, x)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExistenceNotionSeparation.mathematical_existence_notions_separate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

False is a formed proposition without a proof, and Empty is a formed type without a construction. Every explicit construction nevertheless supplies a Nonempty witness.

External model and realization predicates each admit explicit positive and negative examples. The theorem therefore compares the formal notions without elevating one philosophical doctrine into a kernel fact.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExistenceNotionSeparation.HasModel`
- Truth anchor: `D5/S3/ConceptDynamics/ExistenceNotionSeparation.Realized`
- Truth anchor: `D5/S3/ConceptDynamics/ExistenceNotionSeparation.mathematical_existence_notions_separate`
