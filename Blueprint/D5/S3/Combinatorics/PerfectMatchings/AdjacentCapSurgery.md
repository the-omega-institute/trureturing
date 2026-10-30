# Adjacent cap removal in a noncrossing matching

## Abstract

Adjacent cap removal in a noncrossing matching.

**Theorem 1.1 (Adjacent cap removal in a noncrossing matching).**

$$\forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall k \in \operatorname{Fin}\left(m\right),\; \operatorname{SkipPair}\left(j, \operatorname{Partner}\left(\operatorname{CapSurgery}\left(M, j\right), k\right)\right) = \operatorname{ReconnectPartner}\left(M, j, \operatorname{SkipPair}\left(j, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capSurgery_reconnect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The increasing survivor map identifies the smaller partner with the exact original rewiring. The already-paired case and every possible relative order of the two original partners are retained, including an empty surviving frontier.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capSurgery_reconnect`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingIntervals](OrderedMatchingIntervals.md)
