# Finite Helly property for subtrees

## Abstract

Pairwise intersecting connected vertex sets in one tree have a common vertex for every nonempty finite family.

**Theorem 1.1 (A common vertex for a nonempty finite family).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall I \in \operatorname{Type}\left(v\right),\; \operatorname{IsTree}\left(G\right) \Rightarrow \left(\forall a \in I \to \operatorname{Set}\left(V\right),\; \forall s \in \operatorname{Finset}\left(I\right),\; \operatorname{Nonempty}\left(s\right) \Rightarrow \left(\left(\forall i \in I,\; i \in s \Rightarrow \operatorname{Connected}\left(\operatorname{induce}\left(G, a\left(i\right)\right)\right)\right) \Rightarrow \left(\left(\forall i \in I,\; i \in s \Rightarrow \left(\forall j \in I,\; j \in s \Rightarrow \operatorname{Nonempty}\left(\operatorname{inter}\left(a\left(i\right), a\left(j\right)\right)\right)\right)\right) \Rightarrow \left(\exists x \in V,\; \forall i \in I,\; i \in s \Rightarrow x \in a\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SubtreeHelly.inter_nonempty_of_pairwise` (`✓ std3`). ∎

*Citation.* 8e7; original file authors Kyle Miller and Rémi Bottinelli (2026). *Helly property for subtrees of a tree (mathlib PR 39864)*. URL: <https://github.com/8e7/mathlib4/tree/12cb0b6433584e454c4d4577472c4792f0dfe5c9>.

*Commentary.*

The universe levels u and v are independent. V is an arbitrary vertex type in Type u, G is a simple undirected graph on V, and I is an arbitrary index type in Type v. The family a maps I to Set(V), and s is a Finset(I). Assume G.IsTree, s.Nonempty, Connected(G.induce(a(i))) for every i in s, and Nonempty(a(i) intersect a(j)) for every i in s and every j in s. Then there exists x in V belonging to a(i) for every i in s, equivalently the intersection indexed by i in s is nonempty. The formula writes this common-intersection conclusion in membership form. The arrow denotes the function type, and inter denotes set intersection.

Only the selected family is finite: neither V nor I is assumed finite. Indices outside s are unrestricted. The pairwise premise includes equal indices. Native Connected includes a nonempty vertex type, and native IsTree includes connectedness and acyclicity. Thus the hypotheses rule out an empty selected fiber and an empty ambient vertex type, rather than adding a finiteness assumption on either carrier.

A connected induced vertex set in a tree contains the unique simple path between any two of its vertices. Indeed, connectedness gives a walk inside the set; erasing repetitions gives a simple path with support contained in that walk. Acyclicity identifies the paths obtained from any two such walks. Consequently the intersection of two preconnected induced vertex sets is preconnected: the common unique path lies in both sets.

For the crossing step, let a and b be connected induced vertex sets with a common pivot m. Join x in a to m inside a and m to y in b inside b. Their appended walk and an arbitrary x-to-y walk have the same reduced simple path. If y lies in a it is already a crossing vertex. Otherwise choose the boundary dart of that simple path leaving a. Its first vertex lies on the arbitrary walk and in a. The dart cannot come from the first walk, whose vertices all lie in a; it therefore comes from the second walk and its first vertex also lies in b. This constructs a vertex of a intersect b on the arbitrary walk.

For three pairwise intersecting connected induced sets a, b and c, choose a point of c intersect a and a point of b intersect c. Connectedness of c gives a walk between them contained in c. Apply the crossing step for a and b to that walk. The crossing vertex belongs to all three sets.

Induct on the positive cardinality of s. A singleton family has a vertex by connectedness. For at least two indices, choose c in s and erase it. Replace each remaining a(i) by a(i) intersect a(c). Each replacement is nonempty by pairwise intersection and preconnected by unique-path convexity, hence connected. Triple Helly supplies pairwise intersections of the replacements. Induction gives a vertex in all replacements; a remaining index also certifies its membership in a(c), giving a vertex in the original entire family.

For a full finite index type I, G.IsTree together with Connected(G.induce(a(i))) for every i and Nonempty(a(i) intersect a(j)) for every i and j implies Nonempty of the intersection over all i. If I is nonempty, apply the finite-family theorem to Finset.univ using a Fintype presentation of Finite(I). If I is empty, that intersection is Set.univ, so its nonemptiness is exactly Nonempty(V), supplied here by G.IsTree.connected.nonempty. Without a nonempty ambient vertex type the empty-family conclusion would fail.

For a common-source feasibility application, take one source space V equipped with one tree G. For each observation i, let a(i) be the subset of source vertices compatible with that observation. For example a(i) can be the fiber over the prescribed value of an observation map on V. For a nonempty finite set s of observations, assume every such feasibility set induces a connected graph in this same G. If every pair admits a common compatible source vertex, the theorem supplies one source vertex compatible with all observations simultaneously. The sets, their memberships and all witnesses refer to this one source; arbitrary pairwise constraint relations on different spaces do not satisfy these hypotheses merely by being pairwise compatible.

The conclusion concerns finite selected families. No infinite-family intersection conclusion or algorithmic resource bound is asserted. The proof source is 8e7's mathlib PR 39864 at immutable revision 12cb0b6433584e454c4d4577472c4792f0dfe5c9, with original file authors Kyle Miller and Rémi Bottinelli. The owning Library note gives the exact declaration correspondence and Apache-2.0 attribution. This is known subtree-Helly mathematics.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SubtreeHelly.inter_nonempty_of_pairwise`
