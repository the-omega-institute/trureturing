# Triameter and chains of split cliques

## Abstract

The equality cases of the triameter bound by independence are three chains of split cliques.

Let G be a simple undirected graph on a finite vertex type V. The distance between vertices of a connected G is the minimum number of edges in a walk between them. The triameter tr(G) is the maximum of d(x,y)+d(x,z)+d(y,z) over all ordered triples of vertices, with repeats allowed. The independence number α(G) is the largest size of an independent set.

**Definition 1.1 (BlockIndex).**

$$\forall (q: \operatorname{Fin}(3) \to \mathbb{N}), \operatorname{BlockIndex}(q) = \operatorname{Option}(\Sigma (i: \operatorname{Fin}(3)) \operatorname{Fin}(\operatorname{q}(i)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.BlockIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

For q : Fin 3 → ℕ, none indexes the central clique. A pair of leg i and index in Fin (q i) indexes a peripheral clique on that leg.

**Definition 1.2 (block).**

$$\forall (q: \operatorname{Fin}(3) \to \mathbb{N}) (x: \operatorname{EvenLegTriangle.Vertex}(q)), \operatorname{block}(x) = \operatorname{if} \operatorname{Fin.val}(\operatorname{Sigma.snd}(x)) = 0 \operatorname{then} \operatorname{none} \operatorname{else} \operatorname{some}(\langle\operatorname{Sigma.fst}(x), \operatorname{Nat.div}(\operatorname{Fin.val}(\operatorname{Sigma.snd}(x))-1, 2)\rangle)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

For x : EvenLegTriangle.Vertex q, block x returns a BlockIndex q. At positive depth, natural division by two after subtracting one gives the index in Fin (q i).

**Definition 1.3 (Interface).**

$$\forall (q: \operatorname{Fin}(3) \to \mathbb{N}) (x: \operatorname{EvenLegTriangle.Vertex}(q)) (y: \operatorname{EvenLegTriangle.Vertex}(q)), \operatorname{Interface}(x, y) \Leftrightarrow \operatorname{Sigma.fst}(x) = \operatorname{Sigma.fst}(y) \land ((\operatorname{Nat.mod}(\operatorname{Fin.val}(\operatorname{Sigma.snd}(x)), 2) = 0 \land \operatorname{Fin.val}(\operatorname{Sigma.snd}(x))+1 = \operatorname{Fin.val}(\operatorname{Sigma.snd}(y))) \lor (\operatorname{Nat.mod}(\operatorname{Fin.val}(\operatorname{Sigma.snd}(y)), 2) = 0 \land \operatorname{Fin.val}(\operatorname{Sigma.snd}(y))+1 = \operatorname{Fin.val}(\operatorname{Sigma.snd}(x))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.Interface` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

For x y : EvenLegTriangle.Vertex q, an interface links consecutive depths on the same leg whose smaller depth is even. The two cases give the two orientations.

**Definition 1.4 (CliqueChains).**

$$\forall (V: \operatorname{Type}) (G: \operatorname{SimpleGraph}(V)) (q: \operatorname{Fin}(3) \to \mathbb{N}) (f: V \to \operatorname{EvenLegTriangle.Vertex}(q)), \operatorname{CliqueChains}(G, q, f) \Leftrightarrow \operatorname{Function.Surjective}(f)
 \land (\forall x y, x \neq y \longrightarrow \operatorname{block}(\operatorname{f}(x)) = \operatorname{block}(\operatorname{f}(y)) \longrightarrow \operatorname{SimpleGraph.Adj}(G, x, y))
 \land (\forall x y, \operatorname{SimpleGraph.Adj}(G, x, y) \longrightarrow \operatorname{block}(\operatorname{f}(x)) = \operatorname{block}(\operatorname{f}(y)) \lor \operatorname{Interface}(\operatorname{f}(x), \operatorname{f}(y)))
 \land (\forall u v, \operatorname{Interface}(u, v) \longrightarrow \exists x y, \operatorname{SimpleGraph.Adj}(G, x, y) \land \operatorname{f}(x) = u \land \operatorname{f}(y) = v)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.CliqueChains` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

For G : SimpleGraph V, q : Fin 3 → ℕ and f : V → EvenLegTriangle.Vertex q, the four clauses are layers_nonempty, within_cliques, allowed_edges and interfaces_nonempty. The last clause requires one edge over each ordered interface.

**Theorem 1.5 (Hak–Kozerenko Question 1 at k = 1).**

$$\forall (V: \operatorname{Type}) [\operatorname{Fintype}(V)] (G: \operatorname{SimpleGraph}(V)), \operatorname{G.Connected} \longrightarrow (\operatorname{triameter}(G) = 4\cdot\operatorname{SimpleGraph.indepNum}(G)-1 \Leftrightarrow \exists (q: \operatorname{Fin}(3) \to \mathbb{N}) (f: V \to \operatorname{EvenLegTriangle.Vertex}(q)), \operatorname{CliqueChains}(G, q, f))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.question1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

Question 1. Theorem 1.1 determines the distances between the vertices of a triametral triple in graphs attaining the equality in (1), but not the whole graph. Characterize the graphs attaining this equality, at least for k = 1, that is, the graphs G with tr(G) = 4α(G) − 1.

The source assumes at least three vertices. The equivalence uses only finiteness and connectedness and also holds on connected vertex sets of size one or two. Fin(3) indexes the three chains. For each chain i the nonnegative length is q(i), and EvenLegTriangle.Vertex q is the disjoint union over i of depths 0 through 2q(i). A surjection f from V to EvenLegTriangle.Vertex q partitions V into nonempty layers. The three depth-zero layers form the central clique. For each 1 ≤ t ≤ q(i), depths 2t−1 and 2t are the inward and outward layers of clique t on chain i.

CliqueChains requires every pair of distinct vertices in the same clique to be adjacent. Every edge between different cliques joins depth 2t to depth 2t+1 on the same chain i, for 0 ≤ t < q(i). Each such interface has an arbitrary nonempty edge set. At t = 0 the interface starts at the depth-zero layer of chain i in the central clique. A chain of length zero has no interface. The within-clique and interface edges exhaust the graph's edges.

A maximizing triple projects onto three legs with a common point or a triangular centre. Equality in the distance-packing bound forces a triangular centre and even legs. For each central or peripheral block one can choose an independent set of model vertices away from the block. Lifting this set shows that a missing edge within a block would exceed the independence number. The projection also lifts each interface edge. Conversely, each clique contributes at most one vertex to an independent set, and vertices at the ends of the three chains certify the required lower bound on triameter. The general bound then forces equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.BlockIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.CliqueChains`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.Interface`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.block`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.question1`
- Dependency: [D5/S3/Combinatorics/Graph/Triameter/DistanceProjection](DistanceProjection.md)
