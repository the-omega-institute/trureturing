# Structural Independence Criterion

## Abstract

Trivial intersection makes the canonical Galois restriction product bijective.

**Theorem 1.1 (Trivial intersection is structural independence).**

$$\forall F, E, \operatorname{Field}(F) \land \operatorname{Field}(E) \land \operatorname{Algebra}(F, E) \land \operatorname{FiniteDimensional}(F, E) \Rightarrow\\{}\forall A, B\in \operatorname{IntermediateFields}(F, E) \land \operatorname{IsGalois}(F, A) \land \operatorname{IsGalois}(F, B) \land \operatorname{Sup}(A, B) = \operatorname{Top}(F, E), (\operatorname{Inf}(A, B) = \operatorname{Bottom}(F, E) \Rightarrow \operatorname{Bijective}(\operatorname{RestrictionProduct}(A, B)) \land \operatorname{LinearDisjoint}(A, B)) \land\\{}(\forall C\in \operatorname{IntermediateFields}(F, E), \operatorname{IsGalois}(F, C) \land C \neq \operatorname{Bottom}(F, E) \land C \neq \operatorname{Top}(F, E) \Rightarrow\\{}\exists L1, L2\in \operatorname{IntermediateFields}(F, E), \operatorname{IsGalois}(F, L1) \land \operatorname{IsGalois}(F, L2) \land L1 \neq L2 \land \operatorname{Inf}(L1, L2) \neq \operatorname{Bottom}(F, E) \land \neg\operatorname{LinearDisjoint}(L1, L2)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/StructuralIndependenceCriterion.structural_independence_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired restriction homomorphism is constructed from the two normal subextensions. Its kernel is the fixing subgroup of their compositum, so generation of the ambient field makes the map injective.

Trivial intersection is equivalent to linear disjointness for the finite Galois subextensions. The resulting degree product and the Galois automorphism cardinality formula make the canonical restriction map surjective as well.

For the contrast clause, a nontrivial proper Galois subextension is paired with the ambient extension. The two fields are distinct, their intersection is the same nontrivial subextension, and linear disjointness fails.

## References

- Truth anchor: `D5/S3/Factorization/Galois/StructuralIndependenceCriterion.structural_independence_criterion`
