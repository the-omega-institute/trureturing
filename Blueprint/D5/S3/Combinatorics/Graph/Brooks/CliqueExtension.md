# Clique color extensions

## Abstract

A coloring outside a maximum-size clique with one missing edge extends across that copy; clique colorings can also avoid nonconstant prescribed outside colors.

The graph cliqueMinusEdge(k) is the complete graph on Fin(k+2) with the edge between zero and one deleted. A Copy is injective and preserves adjacency; it need not reflect every nonedge.

**Theorem 1.1 (Extending over a clique with one missing edge).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall n \in \mathrm{Nat},\; 3 \le n \Rightarrow \left(\operatorname{maxDegree}\left(G\right) \le n \Rightarrow \left(\operatorname{CliqueFree}\left(G, n + 1\right) \Rightarrow \left(\forall f \in \operatorname{Copy}\left(\operatorname{cliqueMinusEdge}\left(n - 1\right), G\right),\; \operatorname{Colorable}\left(\operatorname{Induce}\left(G, \operatorname{Compl}\left(\operatorname{Range}\left(f\right)\right)\right), n\right) \Rightarrow \operatorname{Colorable}\left(G, n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/CliqueExtension.of_cliqueMinusEdge_copy` (`✓ std3`). ∎

*Citation.* Landon Rabern (2023). *Yet another proof of Brooks' theorem*. DOI: [10.1016/j.disc.2022.113261](https://doi.org/10.1016/j.disc.2022.113261). URL: <https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d>.

*Commentary.*

For n at least three, assume maximum degree at most n and no clique of size n+1. In a copy of the almost-clique, each endpoint of the missing edge has at most one outside neighbor. Choose a common color for those endpoints that avoids both outside colors, then assign the remaining n-1 colors injectively to the other vertices. Degree saturation excludes outside neighbors at those other vertices. In the surgery argument, Hall's theorem supplies a clique coloring that avoids one outside color at each vertex whenever those forbidden colors are not all equal.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/CliqueExtension.of_cliqueMinusEdge_copy`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/ColoringExtension](ColoringExtension.md)
