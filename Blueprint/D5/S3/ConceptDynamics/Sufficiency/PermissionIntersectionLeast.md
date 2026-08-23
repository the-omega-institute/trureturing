# Unique Least Permission Bundle

## Abstract

A sufficient intersection is the unique least sufficient permission bundle.

**Theorem 1.1 (A sufficient intersection is the unique least sufficient bundle).**

$$\begin{gathered}\forall K: \operatorname{Type},\\{}Sufficient: \mathcal{P}(K) \to \operatorname{Prop},\\{}\operatorname{Sufficient}(\operatorname{sInter}(\{P \in \mathcal{P}(K) \mid \operatorname{Sufficient}(P)\})) \Rightarrow \operatorname{IsLeast}(\{P \in \mathcal{P}(K) \mid \operatorname{Sufficient}(P)\}, \operatorname{sInter}(\{P \in \mathcal{P}(K) \mid \operatorname{Sufficient}(P)\})) \land\\{}\exists! Q \in \mathcal{P}(K), \operatorname{IsLeast}(\{P \in \mathcal{P}(K) \mid \operatorname{Sufficient}(P)\}, Q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/PermissionIntersectionLeast.sufficient_intersection_is_unique_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be the type of permission atoms. A permission bundle is a subset of K, and Sufficient is an arbitrary predicate on such bundles. The distinguished bundle is constructed canonically as the intersection of every bundle satisfying that predicate.

If this intersection is itself sufficient, membership in the intersection makes it a subset of every sufficient bundle. Thus it is least among them. Any other least sufficient bundle contains and is contained in the intersection, so antisymmetry proves it is the same bundle.

The public statement exposes both the leastness of the canonical intersection and unique existence of a least bundle. It assumes no upward-closure law; the source describes that law only as typical, outside the named theorem.

Repository search found no exact theorem or duplicate permission primitive. The Lean proof directly applies Mathlib's sInter_subset_of_mem lemma and then subset antisymmetry.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/PermissionIntersectionLeast.sufficient_intersection_is_unique_least`
