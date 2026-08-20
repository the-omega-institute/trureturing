# Gap Endpoints

## Abstract

The three gap right endpoints form a transition cycle of period three, each coordinate being exactly its own gap's length.

The cycle was found while reconciling two enumeration counts that disagreed. The combinatorial closed-itinerary count and a real-coordinate filter differed by exactly three at period nine, and the three words were the rotations of this cycle. The middle step is where the Tribonacci relation enters: the image coordinate is the square of the constant less the constant less one, which is the constant's inverse, which is the small gap's length.

**Theorem 1.1 (The gap endpoints form a three-cycle).**

$$\left(\operatorname{tribonacciPeriodicTransition}\left(\mathit{largeEndpoint}\right) = \mathit{combinedEndpoint} \land \operatorname{tribonacciPeriodicTransition}\left(\mathit{combinedEndpoint}\right) = \mathit{smallEndpoint}\right) \land \operatorname{tribonacciPeriodicTransition}\left(\mathit{smallEndpoint}\right) = \mathit{largeEndpoint}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/EndpointCycle/GapEndpoints.gap_endpoints_form_a_three_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state on this cycle sits on the boundary of its gap, so whether it belongs is a matter of taking gaps closed or half open, not a matter of computing more precisely. Since the cycle has period three it recurs exactly at periods divisible by three, which is where the counts were observed to be unstable.

## References

- Truth anchor: `D5/S0/Tower/EndpointCycle/GapEndpoints.gap_endpoints_form_a_three_cycle`
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration](../DBonacciGeneral/TribonacciPeriodicEnumeration.md)
