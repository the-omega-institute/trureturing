# The 2-neighbour bootstrap percolation number of C_n x P_m is n

## Abstract

In 2-neighbour bootstrap percolation on the direct product of the cycle C_n and the path P_m, the least size of a percolating set is n for every n at least 3 and m at least 1. This settles Problem 5 of Brešar, Hedžet and Herrman.

**Definition 1.1 (The direct product of graphs).**

$$\operatorname{Adj}\left(\operatorname{dirProd}\left(G, H\right), x, y\right) \Leftrightarrow (\operatorname{Adj}\left(G, \operatorname{fst}\left(x\right), \operatorname{fst}\left(y\right)\right) \land \operatorname{Adj}\left(H, \operatorname{snd}\left(x\right), \operatorname{snd}\left(y\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.dirProd` (`✓ std3`).

*Citation.* Boštjan Brešar, Jaka Hedžet, Rebekah Herrman (2024). *Bootstrap percolation and P_3-hull number in direct products of graphs*. DOI: [10.7151/dmgt.2603](https://doi.org/10.7151/dmgt.2603). URL: <https://arxiv.org/abs/2403.10957v1>.

*Commentary.*

The direct product G x H has the pairs (g, h) as vertices; (g, h) and (g', h') are adjacent when g, g' are adjacent in G and h, h' are adjacent in H.

**Definition 1.2 (One round of r-neighbour bootstrap percolation).**

$$\operatorname{step}\left(G, r, A\right) = \operatorname{union}\left(A, \{v \mid r \le \operatorname{card}\left(\operatorname{inter}\left(\operatorname{neighborFinset}\left(G, v\right), A\right)\right)\}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step` (`✓ std3`).

*Citation.* Boštjan Brešar, Jaka Hedžet, Rebekah Herrman (2024). *Bootstrap percolation and P_3-hull number in direct products of graphs*. DOI: [10.7151/dmgt.2603](https://doi.org/10.7151/dmgt.2603). URL: <https://arxiv.org/abs/2403.10957v1>.

*Commentary.*

A round keeps every infected vertex and infects every vertex with at least r infected neighbours: A_t = A_(t-1) together with the vertices v with |N(v) ∩ A_(t-1)| at least r.

**Definition 1.3 (Percolating sets).**

$$\operatorname{Percolates}\left(G, r, A\right) \Leftrightarrow (\exists t \in \mathbb{N},\; \operatorname{iterate}\left(\operatorname{step}\left(G, r\right), t, A\right) = \operatorname{univ})$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.Percolates` (`✓ std3`).

*Citation.* Boštjan Brešar, Jaka Hedžet, Rebekah Herrman (2024). *Bootstrap percolation and P_3-hull number in direct products of graphs*. DOI: [10.7151/dmgt.2603](https://doi.org/10.7151/dmgt.2603). URL: <https://arxiv.org/abs/2403.10957v1>.

*Commentary.*

A set A percolates when some number of rounds, started from A, infects every vertex.

**Definition 1.4 (The bootstrap percolation number m(G, r)).**

$$\operatorname{percolationNumber}\left(G, r\right) = \operatorname{sInf}\left(\{k \mid \exists A \in \operatorname{Finset}\left(V\right),\; \operatorname{Nonempty}\left(A\right) \land \left(\operatorname{card}\left(A\right) = k \land \operatorname{Percolates}\left(G, r, A\right)\right)\}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.percolationNumber` (`✓ std3`).

*Citation.* Boštjan Brešar, Jaka Hedžet, Rebekah Herrman (2024). *Bootstrap percolation and P_3-hull number in direct products of graphs*. DOI: [10.7151/dmgt.2603](https://doi.org/10.7151/dmgt.2603). URL: <https://arxiv.org/abs/2403.10957v1>.

*Commentary.*

m(G, r) is the least size of a nonempty percolating set.

**Definition 1.5 (Problem 5).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; 3 \le n \Rightarrow (1 \le m \Rightarrow (\operatorname{percolationNumber}\left(\operatorname{dirProd}\left(\operatorname{cycleGraph}\left(n\right), \operatorname{pathGraph}\left(m\right)\right), 2\right) = n)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.claim` (`✓ std3`).

*Citation.* Boštjan Brešar, Jaka Hedžet, Rebekah Herrman (2024). *Bootstrap percolation and P_3-hull number in direct products of graphs*. DOI: [10.7151/dmgt.2603](https://doi.org/10.7151/dmgt.2603). URL: <https://arxiv.org/abs/2403.10957v1>.

*Commentary.*

For every n at least 3 and m at least 1, m(C_n x P_m, 2) = n, with C_n the cycle on the vertices 0, ..., n - 1 and P_m the path on the vertices 0, ..., m - 1.

**Theorem 1.6 (Proof).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.result` (`✓ std3`). ∎

*Resolves.* `Problems/bresar-2024-direct-product-cycle-path-percolation` (proved) by `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bresar-2024-direct-product-cycle-path-percolation","declaration_gid":"D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Boštjan Brešar, Jaka Hedžet, Rebekah Herrman (2024). *Bootstrap percolation and P_3-hull number in direct products of graphs*. DOI: [10.7151/dmgt.2603](https://doi.org/10.7151/dmgt.2603). URL: <https://arxiv.org/abs/2403.10957v1>.

*Commentary.*

Upper bound (Proposition 3 of the paper): the layer of the path vertex 0 percolates, since a vertex (a, b + 1) has the two distinct neighbours (a - 1, b) and (a + 1, b) in the layer b, so t rounds infect the layers 0, ..., t. Lower bound: let D(A) be the sum over v in A of |N(v) ∩ A|, twice the number of edges inside A. One round adds a set B disjoint from A in which every vertex has at least 2 neighbours in A; counting the pairs of adjacent vertices in A and B from both sides gives D(A ∪ B) at least D(A) + 4|B|, so 4|A| - D(A) never increases. On the whole vertex set of C_n x P_m the degree of (a, b) is twice the degree of b in P_m, and the degrees of P_m sum to 2(m - 1), so 4|V| - D(V) = 4nm - 4n(m - 1) = 4n. Hence a percolating set A satisfies 4n at most 4|A| - D(A), which is at most 4|A|, and |A| is at least n.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.Percolates`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.dirProd`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.percolationNumber`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step`
