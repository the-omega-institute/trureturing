# Clique and odd-cycle surgery

## Abstract

Rabern surgery colors a regular graph after deleting a maximal independent set whose induced complement exhibits a clique or an odd cycle.

In the formula, card denotes Fintype.card and ComplSubtype(A) is the subtype of vertices outside A. The quantified graph H in the induction hypothesis ranges over the same arbitrary vertex universe as G. Membership(A) denotes the predicate of belonging to A. IsContained is the native adjacency-preserving copy relation.

**Theorem 1.1 (The surgery step).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall A \in \operatorname{Set}\left(V\right),\; [\operatorname{DecidablePred}\left(\operatorname{Membership}\left(A\right)\right)] [\operatorname{Nonempty}\left(\operatorname{ComplSubtype}\left(A\right)\right)] \left(d = \operatorname{maxDegree}\left(G\right) \land \left(3 \le d \land \left(\operatorname{CliqueFree}\left(G, d + 1\right) \land \left(\left(\neg \operatorname{IsContained}\left(\operatorname{cliqueMinusEdge}\left(d - 1\right), G\right)\right) \land \left(\operatorname{IsRegularOfDegree}\left(G, d\right) \land \left(\operatorname{Maximal}\left(\operatorname{IsIndepSet}\left(G\right), A\right) \land \left(\operatorname{maxDegree}\left(\operatorname{Induce}\left(G, \operatorname{Compl}\left(A\right)\right)\right) = d - 1 \land \left(\operatorname{card}\left(V\right) \le k + 1 \land \left(\operatorname{card}\left(\operatorname{ComplSubtype}\left(A\right)\right) \le k \land \left(\left(\left(\neg \operatorname{CliqueFree}\left(\operatorname{Induce}\left(G, \operatorname{Compl}\left(A\right)\right), d\right)\right) \lor \left(\operatorname{maxDegree}\left(\operatorname{Induce}\left(G, \operatorname{Compl}\left(A\right)\right)\right) = 2 \land \operatorname{HasOddCycle}\left(\operatorname{Induce}\left(G, \operatorname{Compl}\left(A\right)\right)\right)\right)\right) \land \left(\forall W \in \mathrm{Type},\; [\operatorname{Fintype}\left(W\right)] \forall H \in \operatorname{SimpleGraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(H\right)\right)] \operatorname{card}\left(W\right) \le k \Rightarrow \left(\operatorname{CliqueFree}\left(H, \operatorname{maxDegree}\left(H\right) + 1\right) \Rightarrow \left(\left(\operatorname{maxDegree}\left(H\right) = 2 \Rightarrow \left(\neg \operatorname{HasOddCycle}\left(H\right)\right)\right) \Rightarrow \operatorname{Colorable}\left(H, \operatorname{maxDegree}\left(H\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Colorable}\left(G, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/Surgery.brooksSurgery` (`✓ std3`). ∎

*Citation.* Landon Rabern (2023). *Yet another proof of Brooks' theorem*. DOI: [10.1016/j.disc.2022.113261](https://doi.org/10.1016/j.disc.2022.113261). URL: <https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d>.

*Commentary.*

Each vertex in the obstruction has one neighbor in the deleted independent set. Adjacent vertices with different such neighbors determine an edge to add to the smaller graph. Its coloring forces different colors at those two neighbors. A clique then admits a Hall coloring avoiding the prescribed colors. For a longer odd cycle, choose a spanning path, assign the first vertex the last outside-neighbor color, and extend along the path. At the final vertex two neighbors share a color, leaving a free color. A three-cycle uses the clique construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/Surgery.brooksSurgery`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/CliqueExtension](CliqueExtension.md)
