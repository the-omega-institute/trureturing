# Finite Escape Pairs

## Abstract

Finite indistinguishable pairs split into persistent and theorem-unique escape.

**Definition 1.1 (Selected escape pairs).**

$$\operatorname{escapePairs}(C, S) = \operatorname{filter}(\operatorname{offDiagonalPairs}(X), \lambda p, \operatorname{indistinguishable}(C, S, p1, p2)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This executable finite-set definition uses the catalog's decidable kernels.

**Definition 1.2 (Unique capture pairs).**

$$\operatorname{uniqueCapturePairs}(C, i) = \operatorname{filter}(\operatorname{escapePairs}(C, \operatorname{without}(C, i)), \lambda p, \neg\operatorname{agrees}(\operatorname{theoremAt}(C, i), p1, p2)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.uniqueCapturePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This executable finite-set definition uses the catalog's decidable kernels.

**Theorem 1.3 (Unique capture is finite difference).**

$$\operatorname{uniqueCapturePairs}(C, i) = \operatorname{escapePairs}(C, \operatorname{without}(C, i)) \setminus \operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.uniqueCapturePairs_eq_sdiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the canonical finite catalog kernel and Mathlib Finset laws.

**Theorem 1.4 (Escape pairs are antitone).**

$$S \subseteq T \Rightarrow \operatorname{escapePairs}(C, T) \subseteq \operatorname{escapePairs}(C, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_anti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the canonical finite catalog kernel and Mathlib Finset laws.

**Theorem 1.5 (Insertion filters escape pairs).**

$$\operatorname{escapePairs}(C, \operatorname{insert}(i, S)) = \operatorname{filter}(\operatorname{escapePairs}(C, S), \lambda p, \operatorname{agrees}(\operatorname{theoremAt}(C, i), p1, p2)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the canonical finite catalog kernel and Mathlib Finset laws.

**Theorem 1.6 (Full escape lies in leave-one-out escape).**

$$\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C)) \subseteq \operatorname{escapePairs}(C, \operatorname{without}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_full_subset_without` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the canonical finite catalog kernel and Mathlib Finset laws.

**Theorem 1.7 (Leave-one-out escape decomposes).**

$$\operatorname{escapePairs}(C, \operatorname{without}(C, i)) = \operatorname{union}(\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C)), \operatorname{uniqueCapturePairs}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_without_eq_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the canonical finite catalog kernel and Mathlib Finset laws.

**Theorem 1.8 (Persistent and unique escape are disjoint).**

$$\operatorname{Disjoint}(\operatorname{escapePairs}(C, \operatorname{fullIndexSet}(C)), \operatorname{uniqueCapturePairs}(C, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_full_disjoint_uniqueCapturePairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the canonical finite catalog kernel and Mathlib Finset laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_anti`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_full_disjoint_uniqueCapturePairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_full_subset_without`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_insert`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.escapePairs_without_eq_union`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.uniqueCapturePairs`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapePairs.uniqueCapturePairs_eq_sdiff`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/RoleSignature](../CIRPT/RoleSignature.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/CatalogKernel](CatalogKernel.md)
