# The outer mixed-count obstruction

## Abstract

For a finite properly three-colored graph with mixed degree two, potential below two at mixed count zero, one, or at least six forces a unique mixed vertex and an adjacent singleton-color leaf.

The vertex set s is finite, but its ambient type may be infinite. Adjacency is symmetric on s and is proper for a coloring into Fin(3); properness also excludes loops on s. Neighborhoods and all color classes are taken inside s. A vertex is mixed when two neighbors have different colors. The potential is the sum of the three reciprocals of class sizes plus one, together with half the sum of the reciprocals of neighborhood sizes plus one. These are the definitions of ThreeColorIncidence.

**Theorem 1.1 (Recovering the exceptional geometry).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorOuterCases.nonisolated_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorOuterCases.nonisolated_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every vertex of s is nonisolated and every mixed vertex has exactly two neighbors. Let m be the number of mixed vertices. If m=0, m=1, or m is at least six, and the potential is less than two, then there are w,l in s such that a vertex v in s is mixed if and only if v=w, the neighborhood of l is exactly {w}, and the entire color class of l inside s is exactly {l}.

Apply the incidence and population reduction to the actual graph. The bound for at least six mixed vertices excludes that range. For at most one mixed vertex, permute the three population indices so that the possible mixed vertex has the first color. The attachment estimate leaves only one mixed vertex and an empty ordinary side opposite a singleton ordinary population; the third-color population in that singleton's class is empty.

Every nonmixed nonisolated vertex belongs to its unique ordinary cell. The empty cells and absence of a mixed vertex in the leaf color therefore identify the full leaf class with the singleton ordinary cell. Every neighbor of this leaf has the mixed vertex's color. If such a neighbor were ordinary, symmetry would place it in the empty opposite cell. Thus every neighbor is the unique mixed vertex; nonisolation makes the neighborhood exactly its singleton.

**Theorem 1.2 (Outer cases with isolates allowed).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorOuterCases.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorOuterCases.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only that adjacency on the finite set s is symmetric, the three-coloring is proper, and each mixed vertex has exactly two neighbors. Empty color classes and isolates are allowed. If the number of mixed vertices is zero, one, or at least six, potential less than two implies the same w,l conclusion: w is the unique mixed vertex, l has neighborhood {w}, and its full color class is {l}. No degree bound is imposed on ordinary vertices, and no size bound is imposed on s.

Remove every isolate to obtain t. Symmetry shows that all neighborhoods of vertices in s are unchanged by this removal, so the mixed set is unchanged. Removing isolates cannot increase the potential; a color class consisting of a lone isolate can give equality. Apply the nonisolated obstruction on t to obtain its mixed vertex and leaf.

The mixed vertex and two differently colored neighbors give a nonisolated member of each of the three colors. If a color has a members in t and r removed isolates, then a is at least one and rho(a)+r/3 is at most rho(a+r)+r/2. Summing yields potential(s) at least potential(t)+|s minus t|/3. The unrestricted reciprocal theorem gives potential(t) at least 23/12. A removed isolate would therefore force potential(s) at least 9/4, contradicting the hypothesis. Thus s=t and the full singleton class and neighborhood carry back unchanged.

For a finite simple graph G, take s to be the full vertex set and adj to be G.Adj. Finite neighborhood cardinality is then G.degree, and both mixedness and potential agree with ColoredReciprocalDeletion. The theorem concerns only the three stated mixed-count ranges; it makes no assertion about counts two through five or the complete Erdős problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorOuterCases.nonisolated_obstruction`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorOuterCases.result`
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorOuterBounds](ThreeColorOuterBounds.md)
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorReciprocal](ThreeColorReciprocal.md)
