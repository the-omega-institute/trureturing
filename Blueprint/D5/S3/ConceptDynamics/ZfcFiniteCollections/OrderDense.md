# OrderDense

## Abstract

Countable dense families admit a generic preorder filter through any prescribed element.

**Theorem 1.1 (A generic filter through a prescribed element).**

$$\forall D, a, \operatorname{Countable}\left(D\right)\implies \exists G, \operatorname{IsGeneric}\left(G, D\right)\land a\in G$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcFiniteCollections/OrderDense.exists_genericFilter_of_countable` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For any preorder, D ranges over families of downward dense sets and a over its elements. If D is countable, there is a nonempty, upward-closed, downward-directed filter G containing a and meeting every set in D. The countable family itself supplies an encodable index type, even when it is empty. On the dual order, each dense set is cofinal. The ideal supplied by Mathlib contains a and meets each indexed set; wrapping that ideal as a preorder filter gives the claim.

Downward density means that every element has a smaller or equal element in the set. Genericity means that the filter meets each dense set in the given family.

The bundled density and genericity interface follows FormalizedFormalLogic/Foundation. The existence proof applies Mathlib idealOfCofinals, mem_idealOfCofinals and cofinal_meets_idealOfCofinals. Attribution and the Apache-2.0 license are in Library/ConceptDynamics/foundation2026firstorder.md.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcFiniteCollections/OrderDense.exists_genericFilter_of_countable`
