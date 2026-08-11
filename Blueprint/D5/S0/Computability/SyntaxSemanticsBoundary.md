# The Syntax-Semantics Boundary

## Abstract

No same-level code type enumerates all predicates on itself.

**Theorem 1.1 (Same-level syntax cannot enumerate full predicate semantics).**

$$\forall Code, \forall semantics: Code\to \operatorname{Set}(Code), \neg\operatorname{Surjective}(semantics).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/SyntaxSemanticsBoundary.same_layer_predicates_not_enumerable` (`✓ std3`). ∎

*Citation.* F. William Lawvere (1969). *Diagonal arguments and cartesian closed categories*. DOI: [10.1007/BFb0080769](https://doi.org/10.1007/BFb0080769).

*Commentary.*

Take any type of codes and any proposed interpretation that assigns to each code a predicate on that same code type. The interpretation cannot be surjective: diagonalization forms the predicate that rejects a code exactly when the predicate assigned to that code accepts it, so the diagonal predicate cannot equal any predicate in the proposed range. Full predicate semantics therefore exceeds every same-level enumeration by syntax. This is the precise cardinal boundary asserted by the source atom; it does not assume a particular programming language or claim that a higher-level semantics has already been constructed.

The library was searched before proving. Pinned Mathlib already contains the exact result as Function.cantor_surjective in its basic function theory; the neighboring declarations Function.exists_fixed_point_of_surjective and Function.cantor_injective were also checked. The Lean theorem is consequently a declared thin honest wrapper that applies the upstream result without reproducing its diagonal proof. A repository search found computability-restricted closure results and finite diagonal escape results, but no existing formal declaration of this unrestricted predicate-enumeration boundary.

## References

- Truth anchor: `D5/S0/Computability/SyntaxSemanticsBoundary.same_layer_predicates_not_enumerable`
