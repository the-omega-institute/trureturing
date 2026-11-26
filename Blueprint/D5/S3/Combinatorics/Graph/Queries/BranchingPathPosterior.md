# The graph posterior after a branching disclosure

## Abstract

A disclosure can return to a branching vertex and use its other slot.

**Definition 1.1 (The incoming pair for a request).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.incoming`

*Formalization.* `D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.incoming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The requested position and the number of already recorded edges select an entry in the history. Use that directed edge as the incoming pair, and use the given initial pair if the index is outside the history.

**Theorem 1.2 (Condition on all the disclosed edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.graph_branching_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.graph_branching_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Draw a world from the prior probability mass function. Each world supplies a simple graph on a common vertex set with a common initial edge. Fix a request schedule on a finite set of positions. Independently of the world, sample an independent uniform permutation of two slots at each position. Each visit to a position uses its same permutation to select among two distinct candidates for the incoming pair. The pair can refer to an earlier edge, selected by the position and the current length of the disclosure. Prepend each returned edge to the history.

For the given reference run, each position uses the same incoming pair whenever it is visited. In each reference row with incoming pair (u, v), the returned vertex y differs from u. The observed table records exactly the positions, slots, and returned values in the reference rows, and the seen set consists of the observed positions. In any world containing the edge from u to v in a reference row, y is a candidate exactly when y is adjacent to v and differs from u.

If the reference disclosure has positive mass, the posterior of a world event is its prior mass restricted to worlds containing every recorded edge and divided by the prior mass of that restriction.

Replay tests the reference values at their actual histories. Inductively, these histories supply valid incoming edges whenever the graph contains every edge already disclosed. The distinct reference slot values at a twice observed position then give the required compatibility. The likelihood for a compatible graph depends only on the number of observed positions, so it cancels.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.graph_branching_posterior`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior.incoming`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior](ForwardPathPosterior.md)
