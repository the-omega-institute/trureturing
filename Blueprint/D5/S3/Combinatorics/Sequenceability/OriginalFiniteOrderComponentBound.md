# Finite-order bounds for original support components

## Abstract

An annihilating order bounds the actual q-containing support components.

**Theorem 1.1 (An annihilator bounds the component count).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/OriginalFiniteOrderComponentBound.q_containing_component_card_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/OriginalFiniteOrderComponentBound.q_containing_component_card_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f label an arbitrary original index type in any additive commutative group, and let E contain exactly all proper inclusion-minimal nonempty zero supports in a finite set Y. Use supportIntersectionGraph E q on all of E. The counted finite set is the image of connectedComponentMk on every vertex containing q. Thus paths may use q-free vertices. If m is a natural number with m at least two and m times f(q) equal to zero, this actual component count is strictly less than m. The number m need only annihilate f(q); it need not be its exact order. There is no ambient finiteness, incidence, injectivity or nonzero-label assumption.

If the count were at least m, select m distinct components and choose a q-containing representative in each. Every selected representative has a nonempty puncture outside {q}: otherwise it is contained in {q}, hence contained in any other selected representative, and minimality forces those original supports to be equal. There is another representative because m is at least two. The singleton equality for supportIntersectionGraphOutside transports component separation to the finite-designated-set charge theorem. That theorem makes the total charge nonzero, while the m singleton charges sum to m times f(q), a contradiction.

When f(q)=0, every q-containing minimal zero support equals {q}. If {q} is a proper subset of Y it is one isolated vertex; otherwise there are no such vertices. The count is therefore zero or one, and the theorem includes this case. The restriction m at least two is necessary: on two original indices q,p with integer labels zero and one, E consists only of {q}, so the count is one even though one annihilates f(q).

The finite representative-selection argument adapts the caller-supplied source, SHA256 98a4f52df6f323420d9d3cb97cb7df1b420a3c4673d9b0ccb6e1172bc87de01c. Its charge obstruction is the general separated_component_charge_sum_ne_zero theorem. No separate graph or decomposition construction is required. No literature novelty is asserted, and no bound for an infinite-order designated label follows.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/OriginalFiniteOrderComponentBound.q_containing_component_card_lt`
- Dependency: [D5/S3/Combinatorics/Sequenceability/BooleanRowChargeConnectivity](BooleanRowChargeConnectivity.md)
