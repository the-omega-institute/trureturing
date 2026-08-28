# Minimal Dependency Support

## Abstract

For a monotone finite support property, inclusion minimality is equivalent to failure after every single deletion.

**Theorem 1.1 (Inclusion and deletion minimality coincide).**

$$\forall property: \operatorname{Finset}\left(Coordinate\right) \to Prop, support: \operatorname{Finset}\left(Coordinate\right),\\{}[\operatorname{DecidableEq}\left(Coordinate\right)],\\{}\operatorname{MonotoneSupport}\left(property\right) \Rightarrow\\{}(\operatorname{InclusionMinimalSupport}\left(property, support\right) \iff \operatorname{DeletionMinimalSupport}\left(property, support\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport.inclusionMinimal_iff_deletionMinimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a property of finite coordinate supports be monotone under inclusion. For any finite support, full inclusion minimality is equivalent to the failure of the property after deleting each selected coordinate.

Decidable equality is retained as an instance binder because deletion uses Finset.erase. Monotonicity remains an explicit antecedent.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport.inclusionMinimal_iff_deletionMinimal`
