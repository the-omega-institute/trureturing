# Periodic phase covers at every finite level

## Abstract

Periodic phase covers at every finite level

For every m>=3 and signed-window radius R, construct m-1 periodic masks. Every mask preserves the initial window, one whole mask preserves each translated future window, and no mask retains three vertices of any m-term progression of step (m+1)^k once k is sufficiently large.

**Theorem 1.1 (The full phase-cover construction).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryPhaseCover.lacunary_phase_cover`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryPhaseCover.lacunary_phase_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale K and all masks are constructed from m and R. The returned bound R<=(m-1)(m+1)^K controls the pseudo-orbit overlap used for the remaining short scales. The masks have a common neighborhood of phase zero and cover every sufficiently short phase window. Long progressions reduce to equally spaced polygons because (m+1)^(k-K) is congruent to one modulo m. Open arcs of length two retain at most two integer-spaced vertices; each interior mask is a union of two arcs of lengths one half and one, each retaining at most one vertex.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryPhaseCover.lacunary_phase_cover`
