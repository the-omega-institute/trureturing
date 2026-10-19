# Brooks' theorem and connected exceptions

## Abstract

Every finite graph that cannot be colored with its maximum degree contains a maximum-degree-plus-one clique or an odd cycle at maximum degree two. Connected exceptions are complete graphs or entire odd cycles.

**Theorem 1.1 (The arbitrary-degree alternative).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \left(\neg \operatorname{Colorable}\left(G, \operatorname{maxDegree}\left(G\right)\right)\right) \Rightarrow \left(\left(\neg \operatorname{CliqueFree}\left(G, \operatorname{maxDegree}\left(G\right) + 1\right)\right) \lor \left(\operatorname{maxDegree}\left(G\right) = 2 \land \operatorname{HasOddCycle}\left(G\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/General.brooks` (`✓ std3`). ∎

*Citation.* Landon Rabern (2023). *Yet another proof of Brooks' theorem*. DOI: [10.1016/j.disc.2022.113261](https://doi.org/10.1016/j.disc.2022.113261). URL: <https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d>.

*Commentary.*

The coloring construction follows Rabern's surgery proof. Delete a maximal independent set, color the smaller induced graph, and extend across its clique or cycle obstruction. The low-degree vertex extension is supplied by its existing coloring theorem. The degree has no upper bound. The vertex type may be empty, and neither connectedness nor regularity is assumed.

**Theorem 1.2 (Complete graphs and entire odd cycles).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{Connected}\left(G\right) \Rightarrow \left(\operatorname{Colorable}\left(G, \operatorname{maxDegree}\left(G\right)\right) \lor \left(G = \operatorname{completeGraph}\left(V\right) \lor \left(\exists n \in \mathrm{Nat},\; \operatorname{Odd}\left(n\right) \land \left(5 \le n \land \operatorname{Nonempty}\left(\operatorname{GraphIso}\left(\operatorname{cycleGraph}\left(n\right), G\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/General.brooks_connected` (`✓ std3`). ∎

*Citation.* Landon Rabern (2023). *Yet another proof of Brooks' theorem*. DOI: [10.1016/j.disc.2022.113261](https://doi.org/10.1016/j.disc.2022.113261). URL: <https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d>.

*Commentary.*

A clique with maximum degree plus one vertices saturates every member's neighbors. No edge can leave it, so connectedness makes it the whole graph. A cycle in a graph of maximum degree at most two likewise saturates every cycle vertex. Connectedness makes its support all vertices and its edges all edges. The cycle length therefore equals the number of vertices. Its native cycle copy is bijective and reflects adjacency because both neighbor sets have cardinality two. A three-cycle is complete; every remaining odd cycle has length at least five. Complete graphs with one, two or three vertices are included.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/General.brooks`
- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/General.brooks_connected`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Surgery](Surgery.md)
