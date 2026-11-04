# A counterexample to Hausmann Question 5.4

## Abstract

The generalized Petersen graph GP(7,2) refutes the full independent-side component-order-three assertion in Hausmann Question 5.4.

**Definition 1.1 (Odd girth exactly five).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{OddGirthFive}\left(G\right) \Leftrightarrow \left(\left(\exists v \in V,\; \exists w \in \operatorname{Walk}\left(G, v, v\right),\; \operatorname{IsCycle}\left(w\right) \land \operatorname{length}\left(w\right) = 5\right) \land \left(\forall v \in V,\; \forall w \in \operatorname{Walk}\left(G, v, v\right),\; \operatorname{IsCycle}\left(w\right) \Rightarrow \left(\operatorname{Odd}\left(\operatorname{length}\left(w\right)\right) \Rightarrow 5 \le \operatorname{length}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.OddGirthFive` (`✓ std3`).

*Citation.* Will Hausmann (2026). *Weighted Max Cut in Subcubic Graphs*. URL: <https://arxiv.org/html/2611.05178v1>.

*Commentary.*

For a simple graph G on V, there is a vertex v and a closed walk w at v that is a simple cycle of length five. Every simple cycle of odd length has length at least five. The universal condition permits even cycles; neither connectivity nor any other restriction is implicit.

**Definition 1.2 (Order of each induced component).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall R \in \operatorname{Set}\left(V\right),\; \operatorname{SmallComponents}\left(G, R\right) \Leftrightarrow \left(\forall C \in \operatorname{ConnectedComponent}\left(\operatorname{induce}\left(G, R\right)\right),\; \operatorname{NatCard}\left(\operatorname{supp}\left(C\right)\right) \le 3\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.SmallComponents` (`✓ std3`).

*Citation.* Will Hausmann (2026). *Weighted Max Cut in Subcubic Graphs*. URL: <https://arxiv.org/html/2611.05178v1>.

*Commentary.*

For every connected component C of the actual induced graph G[R], Nat.card C.supp counts its vertices and is at most three. Since V is finite, these supports are finite. Singleton components are included. This is a component-order bound, not a degree bound, a path-length bound, or a bound on the total size of R.

**Definition 1.3 (The entire universal source assertion).**

$$claim \Leftrightarrow \left(\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)]\left(\forall v \in V,\; \operatorname{degree}\left(G, v\right) \le 3\right) \Rightarrow \left(\operatorname{OddGirthFive}\left(G\right) \Rightarrow \left(\exists L \in \operatorname{Set}\left(V\right),\; \exists R \in \operatorname{Set}\left(V\right),\; \operatorname{Disjoint}\left(L, R\right) \land \left(\operatorname{union}\left(L, R\right) = \operatorname{univ}\left(V\right) \land \left(\operatorname{IsIndepSet}\left(G, L\right) \land \operatorname{SmallComponents}\left(G, R\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.claim` (`✓ std3`).

*Citation.* Will Hausmann (2026). *Weighted Max Cut in Subcubic Graphs*. URL: <https://arxiv.org/html/2611.05178v1>.

*Commentary.*

For every finite vertex type V and simple undirected graph G, degree at most three and odd girth exactly five imply the existence of subsets L and R. They are disjoint, their union is all of V, L is independent, and every component of G[R] has at most three vertices. Fintype and decidable instances express finite presentations and can be supplied classically for every finite graph. There is no size cutoff or connectedness, planarity, regularity, maximum-average-degree, weighting, or construction hypothesis. The claim is the affirmative assertion asked in Question 5.4, not Questions 5.3 or 5.5.

**Theorem 1.4 (The assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hausmann-2026-question-5-4-refutation` (refuted) by `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hausmann-2026-question-5-4-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Will Hausmann (2026). *Weighted Max Cut in Subcubic Graphs*. URL: <https://arxiv.org/html/2611.05178v1>.

*Commentary.*

Use vertices 0 through 13 with edges {0,1}, {0,6}, {0,7}, {1,2}, {1,8}, {2,3}, {2,9}, {3,4}, {3,10}, {4,5}, {4,11}, {5,6}, {5,12}, {6,13}, {7,9}, {7,12}, {8,10}, {8,13}, {9,11}, {10,12}, {11,13}. These are the edges u_i u_(i+1), u_i v_i and v_i v_(i+2), with indices modulo seven and u_i=i, v_i=7+i. The explicit edge list fixes the labels.

The graph is simple, every degree is at most three, and no three vertices form a triangle. The closed walk 0,1,2,9,7,0 is a simple five-cycle. Mathlib's lower bound of three for a simple-cycle length and its equivalence between a three-cycle and a three-clique exclude every shorter odd cycle. These facts establish all the source input conditions on this one graph.

For an arbitrary independent subset L, split on membership of the least undecided vertex. In the inclusion branch its neighbours cannot belong to L. In the exclusion branch that vertex lies outside L. Once four certified outside vertices span a connected tree, the branch terminates. The complete proof tree has 93 nodes and 47 leaves; no maximality or cardinality restriction on L is imposed. At every leaf the four labels are distinct, and the second, third and fourth each have an earlier neighbour. All concrete adjacency and distinctness facts are checked by kernel reduction.

Exhaustiveness of L union R places these four outside vertices in R. The adjacency-to-component lemma puts all four in one connected component of the induced graph. Their distinctness gives an injection from Fin 4 into its support, hence that component has at least four vertices. This contradicts SmallComponents. Thus every possible partition is excluded, and one legal finite graph refutes the universal assertion over all finite graphs.

This refutes the proposed component-order-three structural route. It makes no claim about the weighted 4/5 conjecture, Questions 5.3 or 5.5, minimality of the witness, or literature priority. The known residual-order-six theorem and sparsity-conditioned order-three results do not imply the assertion refuted here.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.OddGirthFive`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.SmallComponents`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.result`
