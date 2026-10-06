# Graph Cycle Space as First Betti Rank

## Abstract

The finite binary graph cycle space has the Euler rank (m-n+c), packaging the graph's first homology rank over (mathbb F_2).

**Theorem 1.1 (Cycle-space Euler rank).**

$$
\operatorname{finrank}_{\mathbf F_2} C_1(G)
= |E(G)| + c(G) - |V(G)|
$$

where (C_1(G)) is the already formalized span of simple-cycle edge indicators and (c(G)) is the number of connected components.

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CycleSpaceEulerRank.graphBettiOne_eq_eulerCycleRank` (`✓ std3`). The proof projects the existing finite_graph_cycle_space theorem: a spanning forest supplies a chord-indexed basis, its cardinality is (m-n+c), and the basis cardinality equals the module finrank. ∎

*Source.* Repository-derived; the cycle-space/H₁ interpretation is standard graph homology over (mathbb F_2).

## Commentary

This is the first explicit bridge from the existing binary endpoint-differential/cycle-space formalization to the standard topological invariant (eta_1(G)). It does not yet encode a simplicial-chain complex or an embedding. Those are the next nodes.

The staged topology bridge is:

1. Register the chain model (C_1\xrightarrow{\partial}C_0) and identify its kernel with the existing simple-cycle space.
2. Add a face-family/2-basis interface for plane embeddings. Mac Lane's criterion says planarity is equivalent to a cycle basis in which every edge occurs in at most two basis cycles.
3. Add the facial cycle double-cover theorem for 2-connected planar graphs.
4. Leave the bridgeless-graph Cycle Double Cover Conjecture as the open frontier; current formal work should target cubic/projective-planar or bounded-genus cases first.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CycleSpaceEulerRank.graphBettiOne_eq_eulerCycleRank`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../../../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
- Mac Lane, “A combinatorial condition for planar graphs”, Fundamenta Mathematicae 28 (1937), 22–32, DOI [10.4064/fm-28-1-22-32](https://doi.org/10.4064/fm-28-1-22-32)
- Seymour, “A survey of the cycle double cover conjecture”, in *Cycles in Graphs* (1985). The conjecture asks whether every bridgeless graph has a family of cycles covering each edge exactly twice.
