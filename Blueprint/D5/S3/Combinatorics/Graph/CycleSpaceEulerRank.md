# Graph Cycle Space as First Betti Rank

## Abstract

The finite binary graph chain model has a first-homology kernel whose rank is m-n+c, where m=|E|, n=|V|, and c is the number of connected components.

**Theorem 1.1 (Boundary-kernel identification and Euler rank).**

$$
H_1(G;\mathbf F_2):=\ker(\partial_G)
=\operatorname{span}_{\mathbf F_2}\{\text{simple-cycle indicators}\},
\qquad
\dim_{\mathbf F_2}H_1(G;\mathbf F_2)=|E|+c-|V|.
$$

*Verification status.* The draft Lean statements have not been compiled locally. No kernel-checked result is claimed. The current kernel/rank statements are definitional projections of existing results and are scaffolding, not new mathematical content.

*Source.* Repository-derived; the cycle-space/H1 interpretation is standard graph homology over F2.

## Commentary

This is a genuine chain-level bridge: edge labels map to the dual of vertex potentials by summing endpoint characters, and the kernel is identified with the existing simple-cycle space. It does not assume an embedding or orient edges, which is appropriate over F2.

The staged topology bridge is:

1. Add the simplicial-chain alias and verify boundary-composition against the endpoint differential.
2. Add a face-family/2-basis interface for plane embeddings. Mac Lane's criterion says planarity is equivalent to a cycle basis in which every edge occurs in at most two basis cycles.
3. Add the facial cycle double-cover theorem for 2-connected planar graphs.
4. Leave the bridgeless-graph Cycle Double Cover Conjecture as the open frontier; target cubic, projective-planar, or bounded-genus cases first.

## References

- Truth anchors: D5/S3/Combinatorics/Graph/CycleSpaceEulerRank.graphFirstHomology_eq_simpleCycleSpace, graphBettiOne_eq_eulerCycleRank
- Dependency: D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace
- Mac Lane, “A combinatorial condition for planar graphs”, Fundamenta Mathematicae 28 (1937), 22–32, DOI https://doi.org/10.4064/fm-28-1-22-32
- Seymour, “A survey of the cycle double cover conjecture”, in Cycles in Graphs (1985). The conjecture asks whether every bridgeless graph has a family of cycles covering each edge exactly twice.
