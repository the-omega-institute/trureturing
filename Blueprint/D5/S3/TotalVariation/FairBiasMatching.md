# Acyclic face matching of the signed fair-bias complex

## Abstract

A matching of the nonempty signed fair-bias faces with a rank decreasing along every oriented cover.

**Theorem 1.1 (An acyclic cover matching with explicit unmatched faces).**

Lean statement: `D5/S3/TotalVariation/FairBiasMatching.actualMatching`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasMatching.actualMatching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite family of columns in a finite binary vector space and a linear order on the signed labels. Suppose a nonempty facet exists. There is a vertex of the first facet and an involution on the nonempty faces. Each nonfixed pair consists of two faces that differ by one vertex. The fixed faces are the singleton of the chosen vertex and the facets equal to their restriction faces.

In each nonsingleton restriction interval, toggle a chosen vertex outside the restriction face. The pair containing the empty face contributes the single unmatched vertex upon restricting to nonempty faces.

Orient the matched covers upward and the other covers downward. A directed edge either moves to an earlier first containing facet or stays in the same interval. Within an interval, upward edges insert the pivot and remove a penalty of two. Downward edges delete a vertex and preserve the pivot's membership. Ordering the facet blocks by the number of earlier facets and adding this local rank gives a natural number that strictly decreases along every directed edge.

**Theorem 1.2 (The augmented matching retains the empty-face pair).**

Lean statement: `D5/S3/TotalVariation/FairBiasMatching.actualAugmentedMatching`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasMatching.actualAugmentedMatching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at least one nonempty facet, each augmented face belongs to a first-facet restriction interval. Choose a common pivot for all faces of each nonsingleton interval and toggle it. Singleton intervals are precisely the full-restriction facets, which are fixed. Every other face has a cover partner.

Keep the empty face and its partner. The same natural rank strictly decreases along unmatched covers directed downward and matched covers directed upward. A nonempty facet supplies a vertex for the first interval. If there are no nonempty facets, the lone augmented face is empty and has no partner.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasMatching.actualAugmentedMatching`
- Truth anchor: `D5/S3/TotalVariation/FairBiasMatching.actualMatching`
- Dependency: [D5/S3/TotalVariation/FairBiasRestriction](FairBiasRestriction.md)
