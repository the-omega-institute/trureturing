# Trapezohedral minimal domination

## Abstract

Closed-private witnesses and the exact labelled one-apex family in a trapezohedral graph.

The graph has distinct labels alpha, beta, a(i), b(i), with cyclic indices in Fin n. Its only edges are alpha--a(i), beta--b(i), a(i)--b(i), and b(i)--a(i+1). The apices are nonadjacent. OEIS A381190, revision 16, asks for the ordinary generating function of connected minimal dominating subsets for every n at least three. Minimal means inclusion minimal among all dominating subsets, independently of connectivity; actual labelled subsets are counted without a symmetry quotient.

**Definition 1.1 (The labelled graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.graph` (`✓ std3`).

*Citation.* Eric W. Weisstein; Joerg Arndt; Peter Luschny; Emily Egolf; Veronika Furst (2026). *OEIS A381190, connected minimal dominating sets in the n-trapezohedral graph*. URL: <https://oeis.org/A381190>.

*Commentary.*

Egolf and Furst, arXiv:2502.05031v1, Definition 3.6, defines this labelled graph. Its four edge families use the canonical cyclic permutation of Fin n for successor. The A381190 counting range is n>=3; the Lean definition also permits auxiliary smaller orders.

**Definition 1.2 (Inclusion minimality).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.MinimalDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.MinimalDominating` (`✓ std3`).

*Citation.* C. M. Mynhardt; A. Roux (2021). *Irredundance Graphs*. URL: <https://arxiv.org/abs/1812.03382v3>.

*Commentary.*

Mynhardt and Roux, section 1.1, defines minimal domination by the absence of a proper dominating subset. Here S is closed dominating and any dominating subset T of S contains all of S. No connectivity condition is imposed on T.

**Definition 1.3 (Closed-private witness).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.ClosedPrivate`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.ClosedPrivate` (`✓ std3`).

*Citation.* C. M. Mynhardt; A. Roux (2021). *Irredundance Graphs*. URL: <https://arxiv.org/abs/1812.03382v3>.

*Commentary.*

Mynhardt and Roux, section 1.1, defines a D-private neighbour as a vertex dominated by s and by no other selected vertex. The closed-neighbourhood convention allows the witness w=s, as the source explicitly notes for isolated vertices of the induced selected subgraph.

**Theorem 1.4 (Closed-private characterization).**

$$\forall (V : Type*), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Set}\left(V\right)), (\operatorname{MinimalDominating}\left(G, S\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(G, S\right)) \land (\forall (s : V), (s \in S) \Rightarrow (\exists (w : V), \operatorname{ClosedPrivate}\left(G, S, s, w\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_private` (`✓ std3`). ∎

*Citation.* C. M. Mynhardt; A. Roux (2021). *Irredundance Graphs*. URL: <https://arxiv.org/abs/1812.03382v3>.

*Commentary.*

Mynhardt and Roux, section 1.1 and Observation 1.1(ii), states the classical characterization: a dominating set is minimal dominating exactly when it is irredundant, meaning that every selected vertex has a private neighbour. The independently proved Lean formulation applies to arbitrary vertex types and compares against all subsets; no novelty is claimed for this general formulation.

**Theorem 1.5 (All proper subsets).**

$$\forall (V : Type*), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Set}\left(V\right)), (\operatorname{MinimalDominating}\left(G, S\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(G, S\right)) \land (\forall (T : \operatorname{Set}\left(V\right)), (\operatorname{StrictSubset}\left(T, S\right)) \Rightarrow (\neg \operatorname{IsDominating}\left(G, T\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_proper` (`✓ std3`). ∎

*Citation.* C. M. Mynhardt; A. Roux (2021). *Irredundance Graphs*. URL: <https://arxiv.org/abs/1812.03382v3>.

*Commentary.*

This restates the inclusion-minimal definition in Mynhardt and Roux, section 1.1: every proper subset fails to dominate, without restricting those subsets to be connected. The Lean equivalence applies to arbitrary vertex types.

**Definition 1.6 (The source counting sequence).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.actualCount`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.actualCount` (`✓ std3`).

*Citation.* Eric W. Weisstein; Joerg Arndt; Peter Luschny; Emily Egolf; Veronika Furst (2026). *OEIS A381190, connected minimal dominating sets in the n-trapezohedral graph*. URL: <https://oeis.org/A381190>.

*Commentary.*

OEIS A381190 defines the count of connected minimal dominating sets in the n-trapezohedral graph, with offset three. Here this is the cardinality of all admissible labelled vertex subsets when n>=3, with a zero formal-series prefix for n<3. Auxiliary paths of small orders are not trapezohedral graph cases.

**Theorem 1.7 (Exact fixed-tag correspondence).**

$$\forall (n : \mathbb{N}), (3 \le n) \Rightarrow (\forall (j : \operatorname{Fin}\left(n\right)), \forall (C : \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Admissible}\left(\operatorname{alphaSet}\left(j, C\right)\right)) \Leftrightarrow ((\operatorname{MinimalCutCover}\left(j, C\right)) \land ((j \in C) \lor (\operatorname{finRotate}\left(n, j\right) \in C))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.alphaSet_admissible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric W. Weisstein; Joerg Arndt; Peter Luschny; Emily Egolf; Veronika Furst (2026). *OEIS A381190, connected minimal dominating sets in the n-trapezohedral graph*. URL: <https://oeis.org/A381190>.

*Acknowledgement.* C. M. Mynhardt; A. Roux (2021). *Irredundance Graphs*. URL: <https://arxiv.org/abs/1812.03382v3>.

*Commentary.*

For n>=3, S={alpha,b(j)} together with selected a-labels C is admissible exactly when C is a minimal cover of every cyclic edge except j, C contains an endpoint of the deleted edge, and C therefore omits an interior label. The first condition governs domination and the selected a-vertices' privacy; the endpoint condition governs induced connectivity; the interior omission is the apex's private witness. Beta is the private witness for b(j). This is a fixed-tag equivalence and does not assert that all admissible sets have such a tag, identify the cut cycle with an ordered path, or establish the original generating series. This fixed-tag equivalence is a repository derivation from the sourced graph and private-neighbour background.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.ClosedPrivate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.MinimalDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.actualCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.alphaSet_admissible_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_private`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.minimalDominating_iff_proper`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](../DominatingSetAverage.md)
