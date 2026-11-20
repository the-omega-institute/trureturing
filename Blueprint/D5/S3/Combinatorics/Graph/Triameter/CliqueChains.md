# Triameter and chains of split cliques

## Abstract

The equality cases of the triameter bound by independence are three chains of split cliques.

Let G be a simple undirected graph on a finite vertex type V. The distance between vertices of a connected G is the minimum number of edges in a walk between them. The triameter tr(G) is the maximum of d(x,y)+d(x,z)+d(y,z) over all ordered triples of vertices, with repeats allowed. The independence number α(G) is the largest size of an independent set.

**Theorem 1.1 (Hak–Kozerenko Question 1 at k = 1).**

$$\forall (V : \operatorname{Type}) [\operatorname{Fintype}(V)] (G : \operatorname{SimpleGraph}(V)), \operatorname{Connected}(G) \longrightarrow (\operatorname{tr}(G) = 4\alpha (G) - 1 \Leftrightarrow \exists (q : \operatorname{Fin}(3) \to \mathbb{N}) (f : V \to \operatorname{Layers}(q)), \operatorname{CliqueChains}(G, q, f))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.question1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

Question 1. Theorem 1.1 determines the distances between the vertices of a triametral triple in graphs attaining the equality in (1), but not the whole graph. Characterize the graphs attaining this equality, at least for k = 1, that is, the graphs G with tr(G) = 4α(G) − 1.

The source assumes at least three vertices. The equivalence uses only finiteness and connectedness and also holds on connected vertex sets of size one or two. Fin(3) indexes the three chains. For each chain i the nonnegative length is q(i), and Layers(q) is the disjoint union over i of depths 0 through 2q(i). A surjection f from V to Layers(q) partitions V into nonempty layers. The three depth-zero layers form the central clique. For each 1 ≤ t ≤ q(i), depths 2t−1 and 2t are the inward and outward layers of clique t on chain i.

CliqueChains requires every pair of distinct vertices in the same clique to be adjacent. Every edge between different cliques joins depth 2t to depth 2t+1 on the same chain i, for 0 ≤ t < q(i). Each such interface has an arbitrary nonempty edge set. At t = 0 the interface starts at the depth-zero layer of chain i in the central clique. A chain of length zero has no interface. The within-clique and interface edges exhaust the graph's edges.

A maximizing triple projects onto three legs with a common point or a triangular centre. Equality in the distance-packing bound forces a triangular centre and even legs. For each central or peripheral block one can choose an independent set of model vertices away from the block. Lifting this set shows that a missing edge within a block would exceed the independence number. The projection also lifts each interface edge. Conversely, each clique contributes at most one vertex to an independent set, and vertices at the ends of the three chains certify the required lower bound on triameter. The general bound then forces equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.question1`
