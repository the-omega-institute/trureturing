# Almost-Everywhere Transformation Description Bound

## Abstract

Eventually affordable reverse transformations give an almost-everywhere description bound, while a null point prevents a pointwise inference.

**Theorem 1.1 (Eventual reverse costs lift to an almost-everywhere complexity bound).**

$$AEEventually(x, \mu, Q, applies(v(x, Q), T(w(x, Q)), w(x, Q)) \land K(transformations, v(x, Q)) + c \leq b(Q) \Rightarrow K(objects, w(x, Q)) \leq K(objects, T(w(x, Q))) + b(Q))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/AlmostEverywhereTransformationDescriptionBound.almost_everywhere_reverse_description_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For almost every sample, suppose the reverse transformation is eventually applicable and its minimum description cost plus the fixed compiler overhead is eventually at most b(Q). The compiled transformation then gives K(w_Q) at most K(T(w_Q)) plus b(Q), eventually on the same full-measure set.

The proof applies the existing one-way transformation-description theorem to the reverse compiler and intersects the two almost-everywhere, eventually filters. Natural-number linear arithmetic discharges the final weakening from reverse cost plus overhead to b(Q).

This is a conditional abstraction of the source's almost-everywhere reverse claim. The repository and pinned Mathlib contain no decimal-to-continued-fraction cylinder comparison, Borel--Bernstein theorem, Lochs theorem, or Dajani--Fieldsteel height law from which the concrete O(log Q) and height-ratio assertions could honestly be derived; those assertions are therefore not made here.

Six-route duplicate search covered keyword and symbol variants, digestion indexes, generalized transformation bounds, and all in-flight math branches. The one-way and bidirectional compiler bounds are proper predecessors, while the existing pointwise/a.e. separation concerns fiber factorization rather than eventual description complexity.

**Theorem 1.2 (An almost-everywhere bound need not hold pointwise).**

$$\forall g: \mathbb{N} \to \mathbb{N}, \exists cost: \mathbb{R} \to \mathbb{N} \to \mathbb{N},\\{}AE(x, Lebesgue, \forall Q, cost(x, Q) \leq g(Q)) \land \forall Q, \neg(cost(0, Q) \leq g(Q)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/AlmostEverywhereTransformationDescriptionBound.almost_everywhere_bound_does_not_imply_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every proposed natural-number bound g, the witness cost equals g(Q) + 1 at zero and equals zero everywhere else. Mathlib's Lebesgue a.e.-not-equal lemma makes the bound hold almost everywhere, whereas every Q explicitly refutes it at the origin.

Lebesgue measure is nonzero, and only its null singleton is exceptional. Thus the separation is not obtained from the vacuous zero measure and it rules out upgrading the first theorem to a pointwise conclusion without additional hypotheses.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/AlmostEverywhereTransformationDescriptionBound.almost_everywhere_bound_does_not_imply_pointwise`
- Truth anchor: `D5/S0/Computability/DescriptionComplexity/AlmostEverywhereTransformationDescriptionBound.almost_everywhere_reverse_description_bound`
- Dependency: [D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound](TransformationDescriptionBound.md)
