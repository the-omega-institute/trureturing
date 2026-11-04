# The Chvatal-Erdos theorem

## Abstract

Deletion connectivity at least the independence bound forces a Hamiltonian cycle.

**Theorem 1.1 (Hamiltonicity with vertex-deletion connectivity unfolded).**

$$\forall V \in \operatorname{Type}\left(\right),\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \operatorname{Nat}\left(\right),\; 3 \le \operatorname{card}\left(V\right) \Rightarrow \left(\left(\forall S \in \operatorname{Set}\left(V\right),\; \operatorname{ncard}\left(S\right) < k \Rightarrow \operatorname{Connected}\left(\operatorname{induce}\left(G, \operatorname{compl}\left(S\right)\right)\right)\right) \Rightarrow \left(\left(\forall S \in \operatorname{Set}\left(V\right),\; \operatorname{IsIndepSet}\left(G, S\right) \Rightarrow \operatorname{ncard}\left(S\right) \le k\right) \Rightarrow \operatorname{IsHamiltonian}\left(G\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ChvatalErdos.isHamiltonian_of_connectivity_independence` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

For every finite vertex type V in any universe, every simple undirected graph G on V and every natural number k, assume that V has at least three vertices. Suppose that for every set S with S.ncard less than k the graph induced on the complement of S is connected. Suppose also that every G-independent set has cardinality at most k. Then G is Hamiltonian. A classical finite enumeration and equality decision are presentations of the finite vertex type, not additional mathematical assumptions.

There is no assumption that k be less than the number of vertices. Complete graphs are Hamiltonian under the stated cardinality bound. Otherwise, two nonadjacent vertices give an independent pair and force k to be at least two. This handles k equal to zero or one without inserting a stronger connectivity premise.

Choose a longest ordinary cycle C. If C fails to span V, choose an outside vertex x and a terminal-clean fan of min(k, C.length) paths from x to C. Use the fixed orientation of C to assign each terminal its successor. Native cycle rotations preserve the dart list up to permutation; injectivity of the first and second dart coordinates makes this a single consistent, injective successor assignment.

An edge between two fan successors joins the two corresponding fan paths into a detour and produces a strictly longer actual cycle. An edge from x to a fan successor gives another such detour. Thus no two fan successors are adjacent, no successor is adjacent to x, and no two fan terminals are consecutive. If the fan had fewer than k paths, its minimum-size bound would saturate all vertices of C, contradicting the absence of consecutive terminals. The fan therefore has at least k paths, and x together with its distinct successors is an independent set of more than k vertices, a contradiction.

The detour is spliced on the induced union of its actual support with C and then mapped injectively into G. The maximal cycle is never assumed to be Hamiltonian on the ambient vertex type. The conclusion is existence of a Hamiltonian cycle, with no algorithmic complexity bound or claim about Hamiltonian-connectedness.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ChvatalErdos.isHamiltonian_of_connectivity_independence`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ConnectivityFan](ConnectivityFan.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CycleDetour](CycleDetour.md)
