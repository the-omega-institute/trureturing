# Compatible Fusion Embedding

## Abstract

An intersection completion is exactly the compatible image of its component completions.

**Theorem 1.1 (The intersection completion embeds as the compatible image).**

$$\begin{gathered}\forall I, Y: \operatorname{Type}, O: I \to \operatorname{Type},\\u: Y \to Y, q: \prod_{i} (Y \to O_{i}),\\\operatorname{let} J := \operatorname{completionEmbedding}\left(\operatorname{componentCompletionRelation}\left(u, q\right)\right);\\\operatorname{Injective}\left(J\right) \land\\(\forall z\in \operatorname{Fused}\left(q\right), \forall i\in I,\\\operatorname{J}\left(\operatorname{completedFusionDynamics}\left(u, q, z\right)\right)_{i} = \operatorname{completedComponentDynamics}\left(u, q, i, \operatorname{J}\left(z\right)_{i}\right)) \land\\\operatorname{range}\left(J\right) = \operatorname{Comp}\left(q\right) \land\\\exists e: \operatorname{Fused}\left(q\right) \equiv \operatorname{Comp}\left(q\right), \forall z\in \operatorname{Fused}\left(q\right), \operatorname{coe}\left(\operatorname{e}\left(z\right)\right) = \operatorname{J}\left(z\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/CompatibleFusionEmbedding.compatible_fusion_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let qi be a family of readouts on a state type Y with update u. Each readout defines complete-future equivalence through the repository's complete itinerary. The fused completion is the quotient by the intersection of these component relations, and J sends a fused class to its class in every component quotient.

The compatible subset Comp consists exactly of component tuples z for which there is one state y whose canonical class in every component is zi. The theorem proves that J is injective, its range is Comp, and the fused quotient is canonically equivalent to Comp with underlying map J.

Advancing both states shifts equality of complete itineraries and therefore preserves every component relation. The induced fused and component updates require no additional hypothesis, and the theorem proves that J intertwines all of them.

Pinned Mathlib supplies Quotient.map and Quotient.exact for the quotient arguments, followed by Equiv.ofInjective and Equiv.setCongr for the canonical equivalence. Repository search found related two-component refinement and product-fullness results, but no declaration containing all four family-indexed conclusions.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/CompatibleFusionEmbedding.compatible_fusion_embedding`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
