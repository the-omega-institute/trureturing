# Existence of total-variation-preserving signed lifts

## Abstract

Every finite signed measure on a Hausdorff Borel quotient of a compact metric space has a total-variation-mass-preserving signed lift.

**Theorem 1.1 (Signed lift with equal total variation mass).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \forall L: \operatorname{Type}\left(v\right), \\\operatorname{CompactMetricBorelSpace}\left(K\right) \land \operatorname{HausdorffBorelSpace}\left(L\right) \Rightarrow\\\forall p: K \to L, \operatorname{Continuous}\left(p\right) \land \operatorname{Surjective}\left(p\right) \Rightarrow\\\forall nu: \operatorname{SignedMeasure}\left(L\right), \\\exists s: \operatorname{SignedMeasure}\left(K\right), \operatorname{map}\left(s, p\right) = nu \land \operatorname{totalVariation}\left(s, \operatorname{univ}\left(\right)\right) = \operatorname{totalVariation}\left(nu, \operatorname{univ}\left(\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLiftExistence.exists_norm_preserving_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* KT. Wu (2026). *The Kuratowski–Ryll-Nardzewski measurable selection theorem*. URL: <https://github.com/LeanPool/lean-pool/blob/7d5e94f7172d47c78cac7f23c0dd01cef1665e42/LeanPool/BicausalOT/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean>.

*Commentary.*

K and L have independent universes. K is any compact metric space with its Borel structure; L is any Hausdorff topological space with its Borel structure. For every continuous surjection p:K to L and every actual finite SignedMeasure nu on L, there is an actual SignedMeasure s on K with map(s,p)=nu and totalVariation(s)(univ)=totalVariation(nu)(univ), an equality in the extended nonnegative reals. Neither carrier nonemptiness nor zero-dimensionality, probability normalization, positivity or finite support is assumed.

Selection.Measurable.exists_measurable_right_inverse supplies a measurable q with p(q(y))=y. Define s=map(nu,q). For each measurable A in L, two applications of VectorMeasure.map_apply give map(s,p)(A)=nu(q-preimage(p-preimage(A)))=nu(A). VectorMeasure.ext proves equality of the actual signed measures; no unprovided map-map lemma is used. VectorMeasure.variation_map_le and SignedMeasure.totalVariation_eq_variation first give mass(s) at most mass(nu); applying them along p gives mass(nu) at most mass(s). Antisymmetry proves equality. SignedMeasure is not assigned a normed-space instance. The upstream selector construction is attributed separately from this project bridge.

On a compact metric totally disconnected K, classical choice applies this existence theorem to every member of an indexed signed-measure family. The selected family satisfies exactly the pushforward and mass premises of NormPreservingLifts.arbitrary_lifts_tendsto. That existing theorem still requires supported clopen rows, a uniform TV bound, eventual fiber constancy for each fixed locally constant test, and a reference weak-star limit. The existence supplier does not construct those data or provide the reference limit. The CH transfinite A–G recursion, future homeomorphism bookkeeping and the analytic conclusions of Kania–Kąkol Problem 8.2 remain outside this theorem.

## References

- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLiftExistence.exists_norm_preserving_lift`
- Dependency: [D5/S3/Topology/Selection/Measurable](../Selection/Measurable.md)
