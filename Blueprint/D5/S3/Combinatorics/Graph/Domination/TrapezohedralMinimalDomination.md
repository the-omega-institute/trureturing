# Trapezohedral minimal domination

## Abstract

Closed-private witnesses and the exact labelled one-apex family in a trapezohedral graph.

The graph has distinct labels alpha, beta, a(i), b(i), with cyclic indices in Fin n. Its only edges are alpha--a(i), beta--b(i), a(i)--b(i), and b(i)--a(i+1). The apices are nonadjacent. OEIS A381190, revision 16, asks for the ordinary generating function of connected minimal dominating subsets for every n at least three. Minimal means inclusion minimal among all dominating subsets, independently of connectivity; actual labelled subsets are counted without a symmetry quotient.

**Definition 1.1 (The labelled graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Four edge families, with successor given by the canonical cyclic permutation of Fin n.

**Definition 1.2 (Inclusion minimality).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.MinimalDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.MinimalDominating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A closed dominating set S such that any dominating subset T of S contains all of S. No connectivity condition is imposed on T.

**Definition 1.3 (Closed-private witness).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.ClosedPrivate`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.ClosedPrivate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex w is dominated by s and by no other selected vertex. The witness w=s is allowed.

**Theorem 1.4 (Closed-private characterization).**

$$\forall (V : Type*), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Set}\left(V\right)), (\operatorname{MinimalDominating}\left(G, S\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(G, S\right)) \land (\forall (s : V), (s \in S) \Rightarrow (\exists (w : V), \operatorname{ClosedPrivate}\left(G, S, s, w\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_private` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Minimal domination is equivalent to domination together with a closed-private witness for each selected vertex. The statement holds for arbitrary vertex types, and its proof compares against all subsets.

**Theorem 1.5 (All proper subsets).**

$$\forall (V : Type*), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Set}\left(V\right)), (\operatorname{MinimalDominating}\left(G, S\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(G, S\right)) \land (\forall (T : \operatorname{Set}\left(V\right)), (\operatorname{StrictSubset}\left(T, S\right)) \Rightarrow (\neg \operatorname{IsDominating}\left(G, T\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_proper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The subset formulation is equivalent to failure of domination for every proper subset, without restricting those subsets to be connected.

**Definition 1.6 (The source counting sequence).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.actualCount`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.actualCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cardinality of the type of all admissible labelled vertex subsets when n>=3, and zero for n<3. Auxiliary paths of small orders are not trapezohedral graph cases.

**Theorem 1.7 (Exact fixed-tag correspondence).**

$$\forall (n : \mathbb{N}), (3 \le n) \Rightarrow (\forall (j : \operatorname{Fin}\left(n\right)), \forall (C : \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Admissible}\left(\operatorname{alphaSet}\left(j, C\right)\right)) \Leftrightarrow ((\operatorname{MinimalCutCover}\left(j, C\right)) \land ((j \in C) \lor (\operatorname{finRotate}\left(n, j\right) \in C))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.alphaSet_admissible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=3, S={alpha,b(j)} together with selected a-labels C is admissible exactly when C is a minimal cover of every cyclic edge except j, C contains an endpoint of the deleted edge, and C therefore omits an interior label. The first condition governs domination and the selected a-vertices' privacy; the endpoint condition governs induced connectivity; the interior omission is the apex's private witness. Beta is the private witness for b(j). This is a fixed-tag equivalence and does not assert that all admissible sets have such a tag, identify the cut cycle with an ordered path, or establish the original generating series.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.ClosedPrivate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.MinimalDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.actualCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.alphaSet_admissible_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_private`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_proper`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](../DominatingSetAverage.md)
