# Represented weak-star subsequence compactness for signed measures

## Abstract

Compact metric signed-measure sequences have represented weak-star subsequences with the same total-variation bound.

K is an arbitrary compact metric space with its Borel measurable structure. For every real C with 0 ≤ C and every sequence s of actual finite SignedMeasure K whose real total variation on univ is at most C, the theorem produces a strictly monotone subsequence and an actual SignedMeasure K limit with the same bound.

**Theorem 1.1 (Actual signed-measure weak-star subsequence supplier).**

$$\begin{aligned}\forall K: Type_{u}, [\operatorname{MetricSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] [\operatorname{MeasurableSpace}\left(K\right)] [\operatorname{BorelSpace}\left(K\right)] \\\forall C: \operatorname{Real}\left(\right), \forall s: \operatorname{Nat}\left(\right) \to \operatorname{SignedMeasure}\left(K\right), \\\operatorname{Nonneg}\left(C\right) \Rightarrow {\forall n: \operatorname{Nat}\left(\right), \operatorname{totalVariationRealUniv}\left(\operatorname{apply}\left(s, n\right)\right) \le C} \Rightarrow\\\exists phi:\operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right), \exists mu:\operatorname{SignedMeasure}\left(K\right), \operatorname{StrictMono}\left(phi\right) \land \operatorname{totalVariationRealUniv}\left(mu\right) \le C \land \operatorname{Tendsto}\left(\operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(\operatorname{compose}\left(s, phi\right)\right)\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(mu\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof writes each signed measure as the difference of its actual Jordan positive and negative finite measures. The pairs with summed mass at most C form a closed subset of the product of two compact finite-measure mass balls, using the pinned Prokhorov compactness theorem and continuity of mass.

The pair-to-functional map is continuous because evaluation at each continuous real test function is the difference of the two continuous finite-measure integrals. Its compact image in the weak dual is metrizable because C(K,Real) is separable for compact metric K. Sequential compactness of the image therefore supplies a strictly monotone subsequence and a point still represented by a finite-measure pair.

The represented limit is the difference of that pair. Vector-measure variation_sub_le and the Jordan mass identity give total variation at most the original C, including C=0 and signed measures of either sign. No Nonempty K, positivity, probability normalization, finite support, or zero-dimensional hypothesis is used; empty K remains covered.

This supplier only provides the reference represented weak-star limit for compact metric successor stages. It does not construct norm-preserving lifts, settle the CH scheduler or recursion, extend to the nonmetrizable final layer, or solve Problem 8.2.

The four-slot escape registration for this theorem remains unfinished under linked issue #5214. The available enrolled templates do not faithfully model this analytic compactness supplier, so no Contract.Registration mirror, compiled registration proof, or current binding evidence is claimed.

## References

- Truth anchor: `D5/S3/Topology/Measures/SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional`
- Dependency: [D5/S3/Topology/Measures/NormPreservingLifts](NormPreservingLifts.md)
