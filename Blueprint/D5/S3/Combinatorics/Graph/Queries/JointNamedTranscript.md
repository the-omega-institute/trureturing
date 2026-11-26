# Conditioning on an actual named transcript

## Abstract

Naming multiplicities in the posterior of a graph observed through complete neighborhoods.

**Theorem 1.1 (Feasible placements have equally many full namings).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.transcript_naming_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.transcript_naming_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix finite vertex and name sets and prescribed initial assignments. Take an actual transcript of a deterministic protocol that queries a name and receives its complete unordered neighborhood or a miss. The reference naming preserves the prescribed assignments. The seen names are the initial names, successful query names and returned neighbor names. Misses rule out their queried names. On a candidate graph, a feasible placement embeds the seen names into the vertices, agrees with the initial assignments and realizes every reported neighbor set as the entire neighborhood of its queried vertex.

The number of full namings that preserve the prescribed assignments and replay the transcript equals the number of feasible placements times a falling factorial. Its base is the number of names remaining after removing the seen and ruled-out names. Its order is the number of vertices outside a placement. Inside each placement, every full naming is an injection of those remaining vertices into the remaining names.

**Theorem 1.2 (The posterior weights each graph by its feasible placements).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.graph_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.graph_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sample a graph index from a prior probability mass function. Independently choose a uniform injection preserving the prescribed initial assignments. Condition on a positive-mass transcript of the same deterministic protocol. The conditional mass of each index equals its prior mass times the number of feasible placements on its graph, divided by the sum of these weights. The common count of naming extensions cancels in the normalization.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.graph_posterior`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/JointNamedTranscript.transcript_naming_count`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/NamedNeighborhoodHistory](NamedNeighborhoodHistory.md)
- Dependency: [D5/S3/Combinatorics/Probability/PartialNameAssignment](../../Probability/PartialNameAssignment.md)
