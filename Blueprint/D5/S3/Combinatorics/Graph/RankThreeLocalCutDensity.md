# Weighted Density from Local Trace Cuts

## Abstract

Hereditary cut bounds on indexed support traces yield a strong seven-coloring at rank three and a weighted density bound without a rank restriction.

Let V be a finite vertex set, I a finite set of owner indices, and A(i) a finite support for each index. Different indices may carry the same support and are counted separately. TraceCap means that for every S contained in V and every L contained in S, at most |S| indexed traces A(i) intersected with S meet both L and S minus L. The condition counts each crossing index once, regardless of its support size. It is imposed on all traces, including those of supports not contained in S.

**Theorem 1.1 (Strong Seven-Coloring for Rank Three).**

$$\forall V \in \mathrm{Finset}\left(Vertex\right),\; \forall I \in \mathrm{Finset}\left(Owner\right),\; \forall A \in \mathrm{Function}\left(Owner, \mathrm{Finset}\left(Vertex\right)\right),\; (\mathrm{SupportRankAtMost}\left(I, A, 3\right) \land \mathrm{TraceCap}\left(V, I, A\right)) \Rightarrow (\exists c \in \mathrm{Function}\left(Vertex, \mathrm{Fin}\left(7\right)\right),\; \mathrm{StrongOnSupportVerticesIn}\left(V, I, A, c\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RankThreeLocalCutDensity.strong_seven_coloring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every indexed support has at most three vertices and TraceCap holds. There is a map from the ambient vertex type to Fin(7) assigning different colors to every two distinct vertices of a common support that both lie in V. Support vertices outside V are allowed and impose no coloring condition. For a trace of size two or three, four times its crossing-cut count is its size times 2 to the power |S|. Traces of size zero or one contribute zero. The empty cut makes the resulting incidence bound strict on every nonempty S: the total incidence of nontrivial traces is less than 4|S|. Thus some vertex belongs to at most three nontrivial indexed traces and has at most six distinct neighbors. Deleting it, coloring inductively, and restoring a missing color constructs the asserted coloring.

For a strong seven-coloring, omit one color and divide the remaining six colors into an ordered choice of three left colors and three right colors. There are 7 times 20 such cuts. A pair of different colors crosses 60 of them, a triple of different colors crosses 108, and each vertex remains available in 120. These counts follow from fixed-size subset counts using binomial coefficients. Apply TraceCap on each available vertex set and double count to obtain 60 times the number of pairs plus 108 times the number of triples at most 120|V|.

**Theorem 1.2 (The Weighted Bound for Arbitrary Support Sizes).**

$$\forall V \in \mathrm{Finset}\left(Vertex\right),\; \forall I \in \mathrm{Finset}\left(Owner\right),\; \forall A \in \mathrm{Function}\left(Owner, \mathrm{Finset}\left(Vertex\right)\right),\; (\mathrm{SupportsContainedIn}\left(V, I, A\right) \land \mathrm{TraceCap}\left(V, I, A\right)) \Rightarrow (5 \cdot \mathrm{CountSupportSize}\left(I, A, 2\right) + 9 \cdot \mathrm{CountSupportSizeAtLeast}\left(I, A, 3\right) \le 10 \cdot \mathrm{card}\left(V\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RankThreeLocalCutDensity.local_cut_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every indexed support is contained in V and TraceCap holds. Write n2 for the number of indices with exactly two support vertices and n3plus for the number with at least three. Then 5 n2 + 9 n3plus is at most 10|V|. There is no upper bound on the original support sizes. Choose a three-element subset of every support of size at least three, leaving smaller supports unchanged. Shrinking supports preserves TraceCap because every crossing of a smaller trace is also a crossing of the original trace. Apply the rank-three coloring and cut count to the shrunken supports. Empty and singleton supports are permitted and contribute zero. Applying this finite combinatorial result to a congruence system requires a separate proof of its hereditary trace capacity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RankThreeLocalCutDensity.local_cut_density`
- Truth anchor: `D5/S3/Combinatorics/Graph/RankThreeLocalCutDensity.strong_seven_coloring`
- Dependency: [D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity](BipartiteSubgraphDensity.md)
