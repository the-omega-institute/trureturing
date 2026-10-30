# Positive Jordan mass through signed clopen sets

## Abstract

Regular positive Jordan mass on an open set is realized above every strict threshold by a signed clopen subset.

K is compact Hausdorff and zero-dimensional with its Borel measurable structure. s is the actual Mathlib real SignedMeasure on K. Both Jordan parts are finite by the Jordan decomposition and are required explicitly to be Regular. For every open V and every real r strictly below the real positive Jordan mass of V, the conclusion supplies a clopen W contained in V with signed mass s(W) strictly above r. No nonemptiness, metrizability, atomicity, positivity of s, or positive-half-mass premise is assumed.

**Theorem 1.1 (Positive clopen signed-mass bridge).**

$$\begin{aligned}\forall K: Type_{u}, [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] [\operatorname{T2Space}\left(K\right)] [\operatorname{ZeroDimensionalSpace}\left(K\right)] [\operatorname{MeasurableSpace}\left(K\right)] [\operatorname{BorelSpace}\left(K\right)] \\\forall s: \operatorname{SignedMeasure}\left(K\right), \\\operatorname{Regular}\left(\operatorname{posPart}\left(\operatorname{toJordanDecomposition}\left(s\right)\right)\right) \Rightarrow\\\operatorname{Regular}\left(\operatorname{negPart}\left(\operatorname{toJordanDecomposition}\left(s\right)\right)\right) \Rightarrow\\\forall V: \operatorname{Set}\left(K\right), \operatorname{IsOpen}\left(V\right) \Rightarrow\\\forall r: Real, r < \operatorname{real}\left(\operatorname{posPart}\left(\operatorname{toJordanDecomposition}\left(s\right)\right), V\right) \Rightarrow\\\exists W: \operatorname{Set}\left(K\right), \operatorname{IsClopen}\left(W\right) \land W \subseteq V \land r < \operatorname{apply}\left(s, W\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/PositiveClopenMass.exists_isClopen_subset_lt_apply_of_lt_posPart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r < 0, the empty clopen set is sufficient. For r ≥ 0, choose b with r < b < p.real(V), where p is the actual positive Jordan part. Mutual singularity gives a measurable N with p(N)=0 and n(Nᶜ)=0. Thus V ∩ Nᶜ retains p mass, and positive regularity gives a compact C inside it with p.real(C)>b.

The negative part n vanishes on C. Negative regularity gives an open O containing C with n.real(O)<b-r. Compactness plus Hausdorffness makes C closed, and the compact zero-dimensional clopen sandwich theorem gives C ⊆ W ⊆ O ∩ V for a clopen W. Finite real monotonicity yields p.real(C) ≤ p.real(W) and n.real(W) ≤ n.real(O); Jordan reconstruction on W then gives s(W)>r.

The proof composes the pinned Mathlib Jordan decomposition, regularity, real-measure monotonicity and compact zero-dimensional clopen-sandwich suppliers; the same-problem ordinary derivation supplied the proof plan. The explicit regularity hypotheses cover all finite and empty cases without infinite-ENNReal cancellation. This is a reusable positive-clopen bridge only: it does not build the CH/Talagrand recursion or prove a full problem resolution. For a clopen V with totalVariation(V)=totalVariation(univ)=1, finiteness gives totalVariation(Vᶜ)=0. Since total variation is the sum of the Jordan parts, the positive part vanishes on Vᶜ, so its mass on V equals its mass on the whole space. With the additional premise 1/2 ≤ posPart.real(univ), the bridge at r=1/3 supplies a clopen W contained in V with s(W)>1/3. Total variation normalization and support alone do not provide the positive-half-mass premise.

## References

- Truth anchor: `D5/S3/Topology/Measures/PositiveClopenMass.exists_isClopen_subset_lt_apply_of_lt_posPart`
