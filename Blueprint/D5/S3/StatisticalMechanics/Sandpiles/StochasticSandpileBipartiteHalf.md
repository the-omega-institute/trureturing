# Stochastically recurrent states of K_{m,n} are at most half of the stable configurations

## Abstract

In the stochastic sandpile model on the complete bipartite graph K_{m,n}, m at least 2 and n at least 1, with the sink in the first part, the stochastically recurrent states number at most half of the n^(m-1) m^n stable configurations, and exactly half if and only if m = 2. This answers Question 6 of Alofi and Dukes: the stochastically recurrent states never dominate the stable states.

**Definition 1.1 (Orientations).**

$$\operatorname{IsOrientation}\left(G, O\right) \Leftrightarrow (\forall u \in V,\; \forall v \in V,\; \operatorname{Adj}\left(G, u, v\right) \Rightarrow (O\left(u, v\right) = \operatorname{true} \Leftrightarrow (O\left(v, u\right) = \operatorname{false})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.IsOrientation` (`✓ std3`).

*Citation.* Amal Alofi, Mark Dukes (2024). *A note on the lacking polynomial of the complete bipartite graph*. DOI: [10.1016/j.disc.2024.114323](https://doi.org/10.1016/j.disc.2024.114323). URL: <https://arxiv.org/abs/2411.02667v1>.

*Commentary.*

An orientation of G directs every edge one way: O(u, v) = true means that the edge uv points from u to v, and then O(v, u) = false.

**Definition 1.2 (In-degree).**

$$\operatorname{indeg}\left(G, O, v\right) = \operatorname{card}\left(\{u \mid \operatorname{Adj}\left(G, u, v\right) \land O\left(u, v\right) = \operatorname{true}\}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.indeg` (`✓ std3`).

*Citation.* Amal Alofi, Mark Dukes (2024). *A note on the lacking polynomial of the complete bipartite graph*. DOI: [10.1016/j.disc.2024.114323](https://doi.org/10.1016/j.disc.2024.114323). URL: <https://arxiv.org/abs/2411.02667v1>.

*Commentary.*

in_O(v) is the number of edges directed into v.

**Definition 1.3 (Stable configurations).**

$$\operatorname{Stable}\left(G, s\right) = \left((v: \{v \mid \operatorname{ne}\left(v, s\right)\}) \to \operatorname{Fin}\left(\operatorname{degree}\left(G, v\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.Stable` (`✓ std3`).

*Citation.* Amal Alofi, Mark Dukes (2024). *A note on the lacking polynomial of the complete bipartite graph*. DOI: [10.1016/j.disc.2024.114323](https://doi.org/10.1016/j.disc.2024.114323). URL: <https://arxiv.org/abs/2411.02667v1>.

*Commentary.*

A stable configuration assigns to every non-sink vertex v a number of grains c(v) with 0 <= c(v) < d(v).

**Definition 1.4 (Stochastically recurrent states).**

$$\operatorname{Sto}\left(G, s\right) = \{c \in \operatorname{Stable}\left(G, s\right) \mid \exists O \in V \to \left(V \to \operatorname{Bool}\right),\; \operatorname{IsOrientation}\left(G, O\right) \land \left(\forall v \in \{v \mid \operatorname{ne}\left(v, s\right)\},\; \operatorname{degree}\left(G, v\right) \le \operatorname{indeg}\left(G, O, v\right) + c\left(v\right)\right)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.Sto` (`✓ std3`).

*Citation.* Amal Alofi, Mark Dukes (2024). *A note on the lacking polynomial of the complete bipartite graph*. DOI: [10.1016/j.disc.2024.114323](https://doi.org/10.1016/j.disc.2024.114323). URL: <https://arxiv.org/abs/2411.02667v1>.

*Commentary.*

Sto(G) is the set of stable configurations c compatible with some orientation O, that is with in_O(v) >= d(v) - c(v) at every non-sink vertex v (Definition 1 and Theorem 2 of the paper).

**Definition 1.5 (Question 6).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; 2 \le m \Rightarrow (1 \le n \Rightarrow (2 \cdot \operatorname{card}\left(\operatorname{Sto}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{inl}\left(0\right)\right)\right) \le n^{m - 1} \cdot m^{n} \land (2 \cdot \operatorname{card}\left(\operatorname{Sto}\left(\operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{inl}\left(0\right)\right)\right) = n^{m - 1} \cdot m^{n} \Leftrightarrow (m = 2)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.claim` (`✓ std3`).

*Citation.* Amal Alofi, Mark Dukes (2024). *A note on the lacking polynomial of the complete bipartite graph*. DOI: [10.1016/j.disc.2024.114323](https://doi.org/10.1016/j.disc.2024.114323). URL: <https://arxiv.org/abs/2411.02667v1>.

*Commentary.*

For m at least 2 and n at least 1, with K_{m,n} the complete bipartite graph on Fin m and Fin n and the sink the vertex 0 of the first part: twice the number of stochastically recurrent states is at most n^(m-1) m^n, with equality if and only if m = 2.

**Theorem 1.6 (Answer).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.result` (`✓ std3`). ∎

*Resolves.* `Problems/alofi-2024-stochastic-sandpile-bipartite-half` (proved) by `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alofi-2024-stochastic-sandpile-bipartite-half","declaration_gid":"D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amal Alofi, Mark Dukes (2024). *A note on the lacking polynomial of the complete bipartite graph*. DOI: [10.1016/j.disc.2024.114323](https://doi.org/10.1016/j.disc.2024.114323). URL: <https://arxiv.org/abs/2411.02667v1>.

*Commentary.*

The vertices of the first part have degree n and those of the second part degree m, so there are n^(m-1) m^n stable configurations. Every orientation directs each of the mn edges into exactly one vertex, so the in-degrees sum to mn; summing in_O(v) + c(v) >= d(v) over the non-sink vertices of a stochastically recurrent c gives at least 2mn - n - mn = n(m - 1) grains. The involution c(v) -> d(v) - 1 - c(v) sends a configuration with S grains to one with (m - 1)(2n - 1) - S grains, so it maps the configurations with at least n(m - 1) grains injectively to those with at most (m - 1)(n - 1) grains, a disjoint set; hence twice the number of stochastically recurrent states is at most the number of stable configurations. For m = 2, direct all n sink edges into the second part, the edge from the non-sink first-part vertex a to b towards b when c(b) = 0 and towards a otherwise; then every configuration with at least n grains is recurrent, and the involution exchanges the configurations with at least n grains and those with at most n - 1, so equality holds. For m at least 3, the configuration with no grain on the first part and m - 2, m - 1, ..., m - 1 grains on the second part has n(m - 1) - 1 grains, which lies in neither set, so the inequality is strict.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.IsOrientation`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.Stable`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.Sto`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.indeg`
- Truth anchor: `D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.result`
