# Local marginal ranks with running intersection

## Abstract

Ranks for ordered families of regional partial traces with running intersection.

**Theorem 1.1 (Subtract adjacent overlap counts).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRunningIntersection.finrank_add_adjacentOverlap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRunningIntersection.finrank_add_adjacentOverlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider downward-closed legal binary words on a finite set of sites. Order the measured regions so that each site's occurrences are consecutive. For any region, count the ordered legal pairs whose occupied union lies entirely within it. The rank over a field of the collected partial traces plus these counts on adjacent intersections equals the sum of the counts on the individual regions.

By the covered-pair rank formula, it suffices to count the union of the sets of pairs supported on each region. The pairs supported on the first region that also occur in a later region are exactly those supported on the intersection with the second region. Indeed, every site of such a pair must occur in the second region by running intersection. Removing the first region and repeating the argument charges each adjacent overlap once.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRunningIntersection.finrank_add_adjacentOverlap`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRank](LocalMarginalRank.md)
