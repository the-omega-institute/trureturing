# Tight inequalities at corners of the path polytope

## Abstract

At the corner given by a word with no adjacent occupied sites, the tight lower bounds and edge inequalities of the path polytope number its dimension plus the occupied interior sites.

For a path with m + 2 sites, the occupancy vectors of binary words with no two adjacent ones are the corners of the polytope cut out by the lower bounds x_i >= 0 and the edge inequalities x_i + x_(i+1) <= 1. With at least two sites the upper bounds x_i <= 1 follow from an edge inequality and a lower bound, so these 2m + 3 inequalities describe the polytope.

**Theorem 1.1 (Tight count at a corner).**

Lean statement: `D5/S1/Words/AdmissibleWords/PathCornerDefect.tight_count_eq_add_interior`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/PathCornerDefect.tight_count_eq_add_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Chvatal (1975). *On certain polytopes associated with graphs*. URL: <https://doi.org/10.1016/0095-8956(75)90041-6>.

*Commentary.*

Let w be a binary word of length m + 2 with no two adjacent ones and x its occupancy vector. The number of lower bounds with x_i = 0 plus the number of edges with x_i + x_(i+1) = 1 equals m + 2 plus the number of occupied sites i with 0 < i < m + 1.

A lower bound is tight exactly at an unoccupied site. Because no edge has both ends occupied, an edge inequality is tight exactly when the edge touches an occupied site, and its indicator is the sum of the two end indicators. Summing over edges counts each occupied site once from its left edge and once from its right edge, except that the first site has no left edge and the last has no right edge. Adding the unoccupied sites gives m + 2 plus the occupied interior sites.

Chvatal showed that for a path these inequalities are exactly the facets. A corner of a d-dimensional polytope is simple when exactly d facets pass through it, so the simple corners of this polytope are exactly the words occupying only endpoints, four of them once there are at least three sites; every other corner lies on one extra facet for each occupied interior site. The facet statement is cited, not proved here. For three sites the only corner that is not simple is the apex 010 of the square pyramid.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/PathCornerDefect.tight_count_eq_add_interior`
- Dependency: [D5/S1/Words/AdmissibleWords/PathStableSetPolytope](PathStableSetPolytope.md)
