# All-Support Circular Marginal Collisions

## Abstract

On every finite labeled support of size at least four, distinct rational probability laws on oriented cycles have all one-label deletion marginals equal.

Let alpha be any type with decidable equality and A any finite set of labels with at least four elements. Cycle(alpha) is Mathlib's quotient of lists by rotation: orientation is retained, and reversal is not identified. A rational finitely supported law is a Finsupp from these actual cycles to the rationals. Deleting label i filters that label from a cycle; pushforward is the actual Finsupp.mapDomain(delete(i)). Mass is the value at unit of the pushforward along the constant map to unit.

**Theorem 1.1 (Disjoint Laws with Every Individual Deletion Marginal Equal).**

$$\forall alpha \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(alpha\right)] \forall A \in \mathrm{Finset}\left(alpha\right),\; (4 \le \mathrm{card}\left(A\right)) \Rightarrow (\exists mu \in \mathrm{Finsupp}\left(\mathrm{Cycle}\left(alpha\right), \mathrm{Rat}\right),\; \exists nu \in \mathrm{Finsupp}\left(\mathrm{Cycle}\left(alpha\right), \mathrm{Rat}\right),\; (\forall C \in \mathrm{Cycle}\left(alpha\right),\; (C \in \mathrm{union}\left(\mathrm{support}\left(mu\right), \mathrm{support}\left(nu\right)\right)) \Rightarrow ((\mathrm{Nodup}\left(C\right)) \land (\mathrm{toFinset}\left(C\right) = A))) \land ((\forall C \in \mathrm{Cycle}\left(alpha\right),\; (0 \le \mathrm{mu}\left(C\right)) \land (0 \le \mathrm{nu}\left(C\right))) \land ((\mathrm{value}\left(\mathrm{mapDomain}\left(\mathrm{constantUnit}, mu\right), \mathrm{unit}\right) = 1) \land ((\mathrm{value}\left(\mathrm{mapDomain}\left(\mathrm{constantUnit}, nu\right), \mathrm{unit}\right) = 1) \land ((\mathrm{Disjoint}\left(\mathrm{support}\left(mu\right), \mathrm{support}\left(nu\right)\right)) \land (\forall i \in alpha,\; (i \in A) \Rightarrow (\mathrm{mapDomain}\left(\mathrm{delete}\left(i\right), mu\right) = \mathrm{mapDomain}\left(\mathrm{delete}\left(i\right), nu\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/AllSupportMarginalCollision.all_support_marginal_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist laws mu and nu on Cycle(alpha). Every cycle in the union of their Finsupp supports has no repeated label and has toFinset exactly A. For every cycle C, both mu(C) and nu(C) are nonnegative. Each law has mass one, and their actual cycle supports are disjoint. For every i in A, the two entire deletion pushforward laws are equal. Thus every label's marginal distribution agrees; no paired or other joint observations from a common sample are supplied by the theorem.

The construction first builds a private Trade(B,m,n) on linear words for every finite B with at least two labels. Its invariants are exact support B without repetition, nonnegative coefficients, mass one on each side, disjoint word supports, equality after erasing each label of B, and equality after sending words to Cycle.ofList. For B={a,b} with a distinct from b, the seed puts unit mass on [a,b] and [b,a] respectively.

For a fresh label x, let P_x prepend x and Q_x append x. The recursive signed interchange sets m' to one half of (push(P_x,m)+push(Q_x,n)) and n' to one half of (push(P_x,n)+push(Q_x,m)). Freshness preserves exact support and no repetition, and averaging preserves nonnegativity and mass one. A word starting with x cannot equal a word ending with x when its remaining nonempty word avoids x. Together with the old disjointness and injectivity at each endpoint, this proves the new word supports disjoint. Erasing x gives the same average of m and n on both sides. Erasing an old label commutes with both endpoint maps, so the previous erasure equality proves the remaining cancellations.

The additional circular invariant is essential. The words x::L and L++[x] represent the same oriented cycle. After Cycle.ofList pushforward the two recursive averages therefore agree by interchange of their summands. Strong induction on finite supports constructs these word trades for arbitrary size; it is used in the public theorem's proof.

Choose p in A and put B=A.erase(p). Push the two word laws forward by L mapped to the cycle of p::L. The fresh anchor gives exact cycle support A and preserves nonnegativity and normalization. CyclicInsertionGap.anchored_coe_injective shows that equality of two such cycles forces equality of their words, so disjoint word supports give disjoint actual cycle supports. For i distinct from p, deleting i commutes with anchoring and uses the word-erasure invariant. Deleting p leaves Cycle.ofList(L), so equality in this case follows from the extra circular invariant. This covers every label in A, including the chosen anchor.

This is a repository-derived construction. The stated range is cardinality at least four; no three-label strengthening or sharp support-cardinality bound is asserted. The result concerns a family of separate marginals, and makes no assertion that those marginals determine a joint observation law.

The literature check distinguishes nearby reconstruction models. The publisher abstract of Permutation Reconstruction (DOI 10.37236/1149) deletes entries of a linear permutation and renumbers the remaining labels. Permutation Reconstruction from Minors (DOI 10.37236/1092) likewise uses order-preserving renumbering after deletions. Reconstructing Permutations from Cycle Minors (DOI 10.37236/108) uses deletion from the disjoint-cycle decomposition of a permutation and reduces larger labels by one. These verified abstracts do not directly state the present fixed-label probability-law theorem on a single oriented cyclic word. Their full theorems are not attributed as this result. No literature novelty claim is made. The specific connection to Diaconis and Sturmfels, Algebraic algorithms for sampling from conditional distributions (DOI 10.1214/aos/1030563990), remains a lead: its full text was not obtained in this check.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/AllSupportMarginalCollision.all_support_marginal_collision`
- Dependency: [D5/S3/Combinatorics/CircularWords/CyclicInsertionGap](CyclicInsertionGap.md)
