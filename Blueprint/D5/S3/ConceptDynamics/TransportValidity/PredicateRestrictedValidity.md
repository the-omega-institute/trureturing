# Predicate-Restricted Validity

## Abstract

Restricting admission by a predicate makes that predicate valid.

**Theorem 1.1 (The restricting predicate is valid on the updated domain).**

$$\forall X \in Sort, A \in X \to Prop, P \in X \to Prop, x \in X,\; \left(A\left(x\right) \land P\left(x\right)\right) \Rightarrow P\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TransportValidity/PredicateRestrictedValidity.predicate_valid_on_restricted_admission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary predicates A and P on X, the updated admission predicate at x is exactly A(x) and P(x). Its right conjunct therefore gives P(x) for every state in the updated domain.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TransportValidity/PredicateRestrictedValidity.predicate_valid_on_restricted_admission`
- Dependency: [D5/S3/ConceptDynamics/TransportValidity/AdmittedValidityReflection](AdmittedValidityReflection.md)
