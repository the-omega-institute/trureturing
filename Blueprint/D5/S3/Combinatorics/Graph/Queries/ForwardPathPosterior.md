# Conditioning on the edges of a disclosed path

## Abstract

The graph posterior after a nonbacktracking path disclosure.

**Definition 1.1 (Schedule of requested slots).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.Schedule`

*Formalization.* `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.Schedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A schedule is a list of pairs containing a position and a Boolean slot.

**Definition 1.2 (A row of the disclosure).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.Entry`

*Formalization.* `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.Entry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row stores the requested position and slot, the state before the step, and the disclosed vertex.

**Definition 1.3 (Replay of the scheduled observations).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.run`

*Formalization.* `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each requested slot, apply the order at its position to the slot, read the corresponding candidate at the current state, record the row, and update the state for the remaining schedule. An empty schedule produces no rows.

**Theorem 1.4 (The path posterior is the prior conditioned on its recorded edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.graph_path_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.graph_path_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Draw a graph world from a probability mass function and independently draw a uniform binary order at each position in a finite set. Start with the same incoming edge in every world. Follow a fixed schedule of positions and slots, shifting the incoming pair after each step. Each world, position and incoming pair specifies two distinct candidate vertices.

Fix the rows of a reference disclosure. The rows never backtrack, each visited position has one common incoming pair, and the partial slot table records precisely the values of the rows. The set of observed positions contains exactly those with at least one recorded slot. In every world containing a row's incoming edge, require that its observed vertex is a candidate exactly when it is a neighbor other than the predecessor.

For a disclosure of positive mass, the posterior probability of any set of worlds equals its prior probability conditional on all recorded edges being present. Replaying the fixed schedule reduces transcript equality to matching the observed slots. Induction along the path shows that compatibility is equivalent to the recorded-edge constraints, because each recorded edge supplies the incoming edge at the next step. The likelihood of the compatible slot table then cancels from numerator and denominator.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.Entry`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.Schedule`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.graph_path_posterior`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.run`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw](PartialForwardOrderLaw.md)
