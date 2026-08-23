# Separating Joins Eliminate Erroneous Merges

## Abstract

A concept that distinguishes two states removes their merge from the canonical product refinement.

**Theorem 1.1 (A separating coordinate eliminates the merged pair).**

$$\begin{gathered}\forall X, B_{C}, B_{D}: \operatorname{Type},\\{}C: X \to B_{C}, D: X \to B_{D}, x, y: X,\\{}D(x) \neq D(y) \Rightarrow \operatorname{conceptJoin}\left(C, D\right)(x) \neq \operatorname{conceptJoin}\left(C, D\right)(y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/SeparatingJoinEliminatesMerge.separating_join_eliminates_merge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current concept C and separating concept D are independent readouts on the same state carrier. Their refinement is the frozen canonical conceptJoin, which maps x to the product coordinate (C(x), D(x)).

If D gives x and y different coordinates, equality of their joined coordinates would force equality in the second product component. Therefore the specific erroneous merge, and hence that concrete pseudo-witness, is absent after refinement.

The proof imports the family concept and join primitives and applies pinned Mathlib's Prod.mk.injEq directly; no replacement join or target-defined object is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/SeparatingJoinEliminatesMerge.separating_join_eliminates_merge`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
