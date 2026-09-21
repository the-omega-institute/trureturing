# Weighted induced deletion

## Abstract

Consider a finite simple graph with a proper coloring by three colors. A mixed vertex has neighbors of two different colors. A collection of mixed vertices of degree two can be deleted at a controlled cost when each of their neighbors is nonmixed and has only that vertex as a mixed neighbor. The control is an inequality between the reciprocal potentials of the original graph and the actual induced graph on the surviving vertices.

**Definition 1.1 (Mixed vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.Mixed`

*Formalization.* `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.Mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mixed(G,c,w) means that there exist vertices r and s adjacent to w with c(r) different from c(s). A nonmixed vertex has a single color throughout its neighborhood whenever that neighborhood is nonempty.

**Definition 1.2 (Reciprocal potential).**

Lean statement: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.potential`

*Formalization.* `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational potential B(G,c) is the sum over the three colors of 1/(class size+1), plus one half of the sum over all vertices of 1/(degree+1). All degrees and class sizes are computed from G and c. Empty color classes contribute one; isolated vertices contribute one half to the vertex term.

**Definition 1.3 (The deficit at a selected vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.debt`

*Formalization.* `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.debt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deficit h(w) is 1/6 minus one half of the sum of 1/(degree(v)+1) over the neighbors v of w. When w has exactly two neighbors r and s, this is 1/6-1/(2(degree(r)+1))-1/(2(degree(s)+1)). The unordered neighborhood sum makes the expression independent of the choice of order of r and s.

**Theorem 1.4 (The simultaneous decrement estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.weighted_induced_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.weighted_induced_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be any finite set of mixed vertices of degree exactly two. For every w in W and each neighbor v of w, assume that v is nonmixed and that every mixed neighbor of v equals w. Assume h(w)>0 for every w in W. Then the sum of h(w) over W is at most B(G,c)-B(G[V\W],c restricted to V\W). Only selected mixed vertices are required to have degree two. There is no lower-bound assumption on either potential, and the empty selection is allowed.

Before deleting w, every neighbor of w survives and retains its original neighborhood: any previously deleted vertex in that neighborhood would be a second mixed neighbor. Write r,s for the two neighbors, d1,d2 for their original degrees, and n for the current size of the color class of w. Nonmixedness puts both complete neighborhoods inside that class, so d1,d2<=n. Positivity of h(w) implies d1,d2>=3. Deletion removes w, decreases each of d1,d2 by one, leaves all other surviving degrees unchanged, and decreases exactly the color class of w by one.

The exact single-deletion potential decrement is 1/6-1/(2d1(d1+1))-1/(2d2(d2+1))-1/(n(n+1)). For each neighbor, the inequalities 2<=d<=n give 1/d+1/(n(n+1))<=2/(d+1). Summing the two comparisons proves that the decrement pays h(w). Finite induction telescopes these inequalities. Induced-neighborhood cardinalities identify every intermediate reciprocal sum with the potential of the corresponding actual induced graph.

For W empty the two potentials agree and the deficit sum is zero. The estimate does not assert a universal lower bound of two for the remaining potential; such a conclusion requires additional graph information.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.Mixed`
- Truth anchor: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.debt`
- Truth anchor: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion.weighted_induced_deletion`
