# Collapse after omitting full-restriction facets

## Abstract

The signed complex with its full-restriction facets removed collapses onto its first simplex.

**Theorem 1.1 (The retained subcomplex collapses to its first simplex).**

Lean statement: `D5/S3/TotalVariation/FairBiasCriticalFacetCollapse.exists_collapse_to_first_facet`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasCriticalFacetCollapse.exists_collapse_to_first_facet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with a signed fair-bias complex having at least one nonempty facet, and order the facets lexicographically by the chosen order on the signed labels. Remove exactly the facets that equal their restriction faces, keeping all proper subfaces. There is a sequence of elementary collapses from the resulting subcomplex to the simplex on the first facet. When a full-restriction facet is removed, its preceding and following retained prefixes agree. At every other step after the first, the elementary pairs from the restriction interval remain present and free in the retained prefix.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasCriticalFacetCollapse.exists_collapse_to_first_facet`
- Dependency: [D5/S3/TotalVariation/FairBiasShellingCollapse](FairBiasShellingCollapse.md)
