# Catalog Joint Kernels

## Abstract

Finite theorem selections compute executable and structural joint kernels.

**Definition 1.1 (Selected-catalog indistinguishability).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two states are indistinguishable when every selected theorem bundle agrees.

**Definition 1.2 (Boolean selected-catalog indistinguishability).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishableB`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishableB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite conjunction of bundle Boolean tests computes indistinguishability.

**Theorem 1.3 (Boolean catalog reflection).**

$$\operatorname{indistinguishableB}(catalog, S, left, right) = true \iff \operatorname{indistinguishable}(catalog, S, left, right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishableB_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Boolean conjunction is true exactly when all selected theorem bundles agree.

**Theorem 1.4 (Catalog indistinguishability is an equivalence).**

$$\operatorname{Equivalence}(\lambda left, right, \operatorname{indistinguishable}(catalog, S, left, right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equivalence is inherited coordinatewise from the selected primitive bundles.

**Definition 1.5 (Catalog joint kernel).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structural kernel is the set of pairs agreeing for every theorem in a Set-level selection.

**Theorem 1.6 (Catalog kernels use the canonical joint kernel).**

$$\operatorname{jointKernel}(catalog, S) = \operatorname{jointKernel}(\lambda i: S, \operatorname{quotientCut}(\operatorname{toKernel}(\operatorname{primitives}(\operatorname{theoremAt}(catalog, i))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel_eq_canonical_jointKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quotient-CUT normalization identifies the catalog relation with the repository's dependent jointKernel.

**Theorem 1.7 (Joint kernels are antitone).**

$$S \subseteq T \Rightarrow \operatorname{jointKernel}(catalog, T) \subseteq \operatorname{jointKernel}(catalog, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every agreement for a larger theorem selection remains an agreement for a smaller selection.

**Theorem 1.8 (Insertion intersects joint kernels).**

$$\operatorname{jointKernel}(catalog, \operatorname{insert}(i, S)) = \operatorname{intersection}(\operatorname{jointKernel}(catalog, S), \{p \mid \operatorname{agrees}(\operatorname{primitives}(\operatorname{theoremAt}(catalog, i)), \operatorname{fst}(p), \operatorname{snd}(p))\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding one theorem intersects the old common kernel with that theorem bundle's kernel.

**Theorem 1.9 (Finite indistinguishability is antitone).**

$$S \subseteq T \Rightarrow \operatorname{indistinguishable}(catalog, T, left, right) \Rightarrow \operatorname{indistinguishable}(catalog, S, left, right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement for a larger finite selection restricts to every smaller selection.

**Theorem 1.10 (Finite insertion adds one conjunct).**

$$\operatorname{indistinguishable}(catalog, \operatorname{insert}(i, S), left, right) \iff \operatorname{agrees}(\operatorname{primitives}(\operatorname{theoremAt}(catalog, i)), left, right) \land \operatorname{indistinguishable}(catalog, S, left, right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable_insert_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Indistinguishability after insertion is exactly the new bundle agreement and the old relation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishableB`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishableB_eq_true_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable_equivalence`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable_insert_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.indistinguishable_mono`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel_antitone`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel_eq_canonical_jointKernel`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.jointKernel_insert`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](TheoremUnit.md)
