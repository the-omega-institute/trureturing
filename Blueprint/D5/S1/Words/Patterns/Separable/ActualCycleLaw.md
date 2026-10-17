# Actual Countable Cycle Law

## Abstract

Actual nonempty shapes determine a normalized marked-cycle law and a common realization of every finite cycle prefix.

A marked cycle records its initial direct or skew sign, every actual right removal shape, and its final actual indecomposable left shape. Each shape has positive length. Right removals flip the sign; the terminal shape uses the resulting sign. A cycle may have no right removals. The mark retains the entire permutation shape at every step.

Let t=sqrt(2)-1, rho=t squared and c=(1-t)/2. Fixed(s,r), denoted F(s,r), contains exactly r right removals before the terminal shape. Its recursive decoder is a bijection from the disjoint union over natural r to the existing unbounded actual cycles of sign s, and preserves total length. Thus the marked cycle space C is countable. Write W(x)=ofReal(rho raised to size(x)), an extended nonnegative weight, on either cycle representation. The probability mass function p on C has exactly these weights.

Omega is C to the natural power, with its product measurable space, and mu is the countable product of the probability measure of p. A tuple gamma in UnboundedTuple(k) retains its ordered k actual marked cycles; nth(k) sends such a tuple to its function on Fin(k), and is bijective. its cylinder [gamma] fixes precisely the first k stream coordinates. For k=0 this cylinder is the whole space. The map res(I) restricts a stream to a finite set I of natural indices. Product(I,p) denotes the finite product measure with coordinate law p.toMeasure.

**Theorem 1.1 (Normalization and actual finite-prefix limits).**

$$\operatorname{Countable}\left(C\right) \land \operatorname{IsProbabilityMeasure}\left(mu\right) \land (\forall k, \operatorname{Bijective}\left(\operatorname{nth}\left(k\right)\right)) \land (\forall s,r, \sum_{x\in \operatorname{F}\left(s, r\right)}\operatorname{W}\left(x\right)=\operatorname{ofReal}\left(c\cdot t^{r}\right)) \land (\sum_{x\in C}\operatorname{W}\left(x\right)=1) \land (\forall k,gamma\in \operatorname{UnboundedTuple}\left(k\right), \operatorname{MeasurableSet}\left(\operatorname{cyl}\left(gamma\right)\right) \land \operatorname{mu}\left(\operatorname{cyl}\left(gamma\right)\right)=\operatorname{W}\left(gamma\right)) \land (\forall k,gamma\in \operatorname{UnboundedTuple}\left(k\right), \exists K,H,d\in \operatorname{Tuple}\left(K, H, k\right), \operatorname{erase}\left(d\right)=gamma \land \lim_{n\to\infty}\operatorname{p}\left(d, n\right)=\operatorname{toReal}\left(\operatorname{mu}\left(\operatorname{cyl}\left(gamma\right)\right)\right)) \land \operatorname{iIndepFun}\left(coordinates, mu\right) \land (\forall I\in \operatorname{Finset}\left(N\right), \operatorname{map}\left(mu, \operatorname{res}\left(I\right)\right)=\operatorname{Product}\left(I, p\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/ActualCycleLaw.actual_countable_cycle_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here s ranges over both Boolean cut signs, r and k over natural numbers, gamma over all unbounded k-tuples, and I over finite sets of natural indices. The mass of F(s,r) is ofReal(c*t^r), and the mass of all marked cycles is one. Every prefix cylinder is measurable and has mass W(gamma), using its total size. For every gamma there are finite K,H and a bounded actual tuple d whose erasure is gamma and whose actual uniform-permutation probability converges to the real mass of [gamma]. The function p(d,n) in the formula is Tuple.probability: it is the actual EventFor mass when n exceeds its original threshold and zero otherwise. The limit is along all natural source sizes.

The coordinate cycles on this one stream are independent and every finite restriction has its corresponding product law. This asserts independence between complete cycles. Within one cycle all shapes and the alternating signs belong to the same mark; no independence between its terminal type and its number of low-value removals is used or asserted.

The actual critical shape counts give total right-shape weight t and total terminal-shape weight c for either sign. A recursive bijection preserves both these actual shape carriers and every length. Therefore exactly r removals have weight c*t^r for each initial sign. Summing the geometric series gives 2*c/(1-t)=1. This proves normalization before forming the probability mass function. The product-measure cylinder formula then multiplies the actual weights, and length additivity gives W(gamma). The existing actual finite-tuple count-ratio limit identifies each such cylinder mass with a finite-permutation limit.

A common marked-cycle stream is not yet a reconstructed infinite permutation. This result does not prove equality of actual history events across different caps, all position or label cutoff observations, the low-removal and terminal-type joint distribution, or the conditional predictable hazard. Literal position and label transport, the precycle filtration and the occupation and marginal discrepancy hypotheses remain separate mathematical requirements.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/ActualCycleLaw.actual_countable_cycle_law`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCycles](ActualCycles.md)
