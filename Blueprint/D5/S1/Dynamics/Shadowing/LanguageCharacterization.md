# A finite-language criterion for neighborhood shadowing

## Abstract

A finite-language criterion for neighborhood shadowing

Question 5.5 of Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, asks for a language characterization of neighborhood two-shadowing for subshifts.

**Theorem 1.1 (Forbidden hyperedges and color classes).**

Lean statement: `D5/S1/Dynamics/Shadowing/LanguageCharacterization.anchoredColoring_iff_no_monochromatic_edge`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LanguageCharacterization.anchoredColoring_iff_no_monochromatic_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertices are the positive times in the finite word. A hyperedge is an inclusion-minimal set of times whose selected blocks cannot occur with the initial block in a single language word. A color class extends with the anchor exactly when it contains no hyperedge. Every nonextendible color class contains an inclusion-minimal nonextendible subset.

**Theorem 1.2 (Neighborhood N-shadowing and anchored language coloring).**

Lean statement: `D5/S1/Dynamics/Shadowing/LanguageCharacterization.neighborhoodFiniteShadowing_iff_languageColoring`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LanguageCharacterization.neighborhoodFiniteShadowing_iff_languageColoring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a closed two-sided subshift over a finite discrete alphabet, a compatible metric, and a positive integer N. Neighborhood N-shadowing holds exactly when for every radius k there is a radius m at least k with the following property. For every length parameter n and every word on [-m,n+m] whose radius-m blocks at times 0 through n occur in the language, the times 1 through n admit a coloring with N colors. Each color has a language word on [-k,n+k] that agrees with the original word on the initial radius-k block and on the radius-k block at every time of that color.

For necessity, realize the locally admissible blocks as a finite pseudo-orbit and continue it by an exact orbit. The small initial diameter and tracing at time zero put the entire tracer tuple in the initial cylinder. The block at each positive time is assigned a color by choosing one of those tracers.

For sufficiency, glue the overlapping blocks of a pseudo-orbit and use the finite criterion on each restriction. The resulting nonempty sets of anchored tuples covering a finite prefix form a decreasing sequence of closed subsets of the compact tuple space. A tuple in their intersection traces at every time. The symmetric coordinate windows form an entourage basis, and every compatible metric induces the product uniformity on the compact subshift. Taking N equal to two gives the criterion in Question 5.5.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/LanguageCharacterization.anchoredColoring_iff_no_monochromatic_edge`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LanguageCharacterization.neighborhoodFiniteShadowing_iff_languageColoring`
- Dependency: [D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift](LacunaryProgressionSubshift.md)
