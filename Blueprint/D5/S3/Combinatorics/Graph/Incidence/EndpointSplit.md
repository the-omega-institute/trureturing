# Splitting a root graph at its endpoint partitions

## Abstract

Endpoint partitions split a simple graph into tagged blocks.

**Definition 1.1 (A setoid at each endpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.EndpointPartition`

*Formalization.* `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.EndpointPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each vertex take a setoid on the edges incident to it. Its quotient has one element per nonempty class. A tagged block is a vertex together with one of its quotient classes. The split graph joins the two tagged classes of each edge. Projecting a split edge to the two tags recovers the original edge, so simple roots give a bijection of edge sets.

**Theorem 1.2 (Blocks are inhabited).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.members_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.members_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each block has at least one member, by quotient surjectivity.

**Theorem 1.3 (Membership in a split edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.mem_splitPair_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.mem_splitPair_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tagged block belongs to the split pair of a root edge exactly when the edge is incident at its tag and its incident label has that quotient class.

**Theorem 1.4 (The split preserves edge count).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.card_edgeSet`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.card_edgeSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split graph and the root have the same edge cardinality.

**Theorem 1.5 (Lifting connectivity to the split).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.splitGraph_connected_of_steps`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.splitGraph_connected_of_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A connected graph on the root edges gives a connected split graph if every adjacent pair of labels has a common split block. Use the adjacency step through that block and both ends of a split edge.

**Theorem 1.6 (Projecting connectivity from the split).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.connected_of_splitGraph_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.connected_of_splitGraph_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A connected split graph gives a connected graph on root edges if every block has connected member labels there. Follow a split walk and transfer each step across the label it shares.

**Theorem 1.7 (Each root edge contributes two labels).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.card_total_members`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.card_total_members` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a finite root, the sum of the block member cardinalities is twice the edge count, by the equivalence with marked endpoint incidences.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.EndpointPartition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.card_edgeSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.card_total_members`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.connected_of_splitGraph_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.mem_splitPair_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.members_nonempty`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.splitGraph_connected_of_steps`
