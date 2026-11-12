# Bounded cliques without finite open chromatic number

## Abstract

The deleted square of beta Nat has bounded cliques for every closed orthogonality, but its swap graph admits no finite open independent cover.

**Definition 1.1 (The actual deleted square).**

$$\forall u: UniverseLevel, \forall K: Type_{u}, \operatorname{DeletedSquare}\left(K\right) = \{z: K \times K \mid \operatorname{fst}\left(z\right) \neq \operatorname{snd}\left(z\right)\}$$

*Formalization.* `D5/S3/Topology/StoneCech/DeletedSquareChromatic.DeletedSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

DeletedSquare K is the subtype of ordered unequal pairs in K times K, with exactly the induced product topology. It inherits Hausdorffness when K is Hausdorff. For the endpoint K is the compact Stone space of all ultrafilters on Nat, homeomorphic to the Stone–Cech compactification of discrete Nat.

**Definition 1.2 (Universal bounded-clique property).**

$$\forall u: UniverseLevel, \forall X: Type_{u}, [\operatorname{TopologicalSpace}\left(X\right)], {\operatorname{BoundedCliqueProperty}\left(X\right)} \Leftrightarrow {\forall G: \operatorname{SimpleGraph}\left(X\right), {\operatorname{IsClosed}\left(\operatorname{AdjSet}\left(G\right)\right)} \Rightarrow \exists N: Nat, \forall S: \operatorname{Set}\left(X\right), {\operatorname{IsClique}\left(G, S\right)} \Rightarrow {\operatorname{Finite}\left(S\right)} \land {\operatorname{ncard}\left(S\right) \le N}}$$

*Formalization.* `D5/S3/Topology/StoneCech/DeletedSquareChromatic.BoundedCliqueProperty` (`✓ std3`).

*Citation.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

A SimpleGraph is exactly an arbitrary symmetric irreflexive binary relation. AdjSet G is the set of all pairs (x,y) with G.Adj x y, in the entire product X times X, including its diagonal. Every subset S whose distinct pairs are related is quantified over. The conclusion requires finiteness as well as the ncard bound; it does not use ncard's zero value on infinite sets to hide infinite cliques. The bound may depend on G.

**Definition 1.3 (Universal finite open chromatic property).**

$$\forall u: UniverseLevel, \forall X: Type_{u}, [\operatorname{TopologicalSpace}\left(X\right)], {\operatorname{FiniteOpenChromaticProperty}\left(X\right)} \Leftrightarrow {\forall G: \operatorname{SimpleGraph}\left(X\right), {\operatorname{IsClosed}\left(\operatorname{AdjSet}\left(G\right)\right)} \Rightarrow \exists m: Nat, \exists U: \operatorname{Fin}\left(m\right) \to \operatorname{Set}\left(X\right), \operatorname{OpenIndependentCover}\left(G, U\right)}$$

*Formalization.* `D5/S3/Topology/StoneCech/DeletedSquareChromatic.FiniteOpenChromaticProperty` (`✓ std3`).

*Citation.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

OpenIndependentCover G U means every U(i) is open, every point lies in at least one U(i), and for every i no two points in U(i) are adjacent. There is no partition or disjointness requirement. Both zero and one proposed colors remain in the quantifier m : Nat. The property again quantifies over every whole-product closed symmetric irreflexive relation.

**Definition 1.4 (The coordinate-swap orthogonality).**

$$\forall u: UniverseLevel, \forall K: Type_{u}, \forall x: \operatorname{DeletedSquare}\left(K\right), \forall y: \operatorname{DeletedSquare}\left(K\right), \operatorname{Adj}\left(\operatorname{swapGraph}\left(K\right), x, y\right) \Leftrightarrow {\operatorname{fst}\left(x\right) = \operatorname{snd}\left(y\right)} \land {\operatorname{snd}\left(x\right) = \operatorname{fst}\left(y\right)}$$

*Formalization.* `D5/S3/Topology/StoneCech/DeletedSquareChromatic.swapGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every type K this is a SimpleGraph on DeletedSquare K. Symmetry reverses the two equalities, and a self-edge would equate the two coordinates of a deleted-square point. When K is Hausdorff, the two equality sets are closed in the entire product of the deleted square with itself.

**Theorem 1.5 (Countable compactness of the full countable power).**

$$\forall u: UniverseLevel, \forall K: Type_{u}, [\operatorname{TopologicalSpace}\left(K\right)], [\operatorname{CompactSpace}\left(K\right)], [\operatorname{T2Space}\left(K\right)], [\operatorname{ExtremallyDisconnected}\left(K\right)], \operatorname{CountablyCompactSpace}\left(Nat \to \operatorname{DeletedSquare}\left(K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/DeletedSquareChromatic.countablyCompactSpace_deletedSquare_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem applies to arbitrary compact Hausdorff extremally disconnected K, with its given topology. Countable compactness is the native countable-open-cover property, equivalently that every sequence has a cluster point. Neither sequential compactness nor a general product theorem for countably compact spaces is used.

On each infinite pool, enumerate the pool increasingly and apply the native PointPairSeparation eventual-equality theorem contrapositively. If no clopen separates infinitely many pairs in either orientation, each fixed clopen test eventually agrees, forcing eventual equality and contradicting the deleted-square condition. Complementation turns this into an oriented clopen separator. Repeat for each coordinate, retaining decreasing infinite pools. The native diagonal_pool supplies an infinite pseudointersection; injective enumeration makes the exceptional preimage finite for every coordinate.

Embed the countable power of DeletedSquare K into the compact ambient product Nat to K times K by taking subtype values coordinatewise. A cluster point of the thinned sequence belongs to every fixed closed rectangle C(j) times complement(C(j)), because the corresponding tail lies there. Thus every coordinate stays off the diagonal. The inducing product embedding transfers the cluster point back to the deleted-square power, and the cofinal increasing subsequence transfers it to the original sequence.

**Theorem 1.6 (The countable-power criterion for all closed orthogonalities).**

$$\forall u: UniverseLevel, \forall X: Type_{u}, [\operatorname{TopologicalSpace}\left(X\right)], [\operatorname{CountablyCompactSpace}\left(Nat \to X\right)], \operatorname{BoundedCliqueProperty}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/DeletedSquareChromatic.boundedCliqueProperty_of_countablyCompact_power` (`✓ std3`). ∎

*Citation.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

This is Feldman–Wilce Theorem 1, formalized independently from the mathematical argument. Constant-coordinate sequences transfer the power cluster property to X. An infinite clique sequence has a cluster point x; every neighborhood rectangle of (x,x) contains two terms of distinct indices. Closedness then gives a loop, a contradiction. This excludes every infinite clique subset by a choice of an injective natural-number sequence in it.

If finite clique sizes had no uniform bound, choose an (n+1)-point clique for each n, enumerate its entries in the first n+1 coordinates, and pad with its last entry. A cluster point q of this sequence in Nat to X satisfies adjacency between q(i) and q(j) for all distinct i and j: the corresponding pairs lie eventually in the closed adjacency set. Applying the previous cluster-point contradiction to q gives the uniform bound. No closedness restriction away from the diagonal or separation axiom is added to this criterion.

**Theorem 1.7 (The swap graph excludes every finite open independent cover).**

$$\forall m: Nat, \forall U: \operatorname{Fin}\left(m\right) \to \operatorname{Set}\left(\operatorname{DeletedSquare}\left(\operatorname{Ultrafilter}\left(Nat\right)\right)\right), \neg{\operatorname{OpenIndependentCover}\left(\operatorname{swapGraph}\left(\operatorname{Ultrafilter}\left(Nat\right)\right), U\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/DeletedSquareChromatic.no_finite_open_independent_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

The swap graph relates (p,q) to (r,s) exactly when p=s and q=r. These two equality conditions make its adjacency set closed in the whole product. Swapping is symmetric, and deleting the diagonal makes the graph irreflexive.

For distinct natural principal points a,b, record every color containing (a,b). Color an unordered pair a<b by the ordered pair of its two full membership patterns. Reuse Yann Pequignot's Apache-2.0 relativized infinite Ramsey theorem from NathansonProblem9, with its original proof and attribution intact. It yields an infinite A and fixed directional patterns P,Q. Independence makes P and Q disjoint.

Split A into disjoint infinite supports A0,A1 with the native split_pool. Extend cofinite intersect principal(Ai) to free ultrafilters p,q. The supports force p distinct from q. A cover member containing (p,q) contains a relative basic clopen rectangle. Intersect the rectangle's supports with A0,A1. Freeness makes both resulting supports infinite and hence unbounded in Nat. One principal pair in the rectangle has increasing order; another has decreasing order. Homogeneity puts the same color in P and Q, a contradiction. These two pairs need not be swaps. Full patterns retain the exact argument for overlapping covers.

**Theorem 1.8 (Strictness of the second implication).**

$${\operatorname{T2Space}\left(\operatorname{DeletedSquare}\left(\operatorname{Ultrafilter}\left(Nat\right)\right)\right)} \land {{\operatorname{BoundedCliqueProperty}\left(\operatorname{DeletedSquare}\left(\operatorname{Ultrafilter}\left(Nat\right)\right)\right)} \land {\neg{\operatorname{FiniteOpenChromaticProperty}\left(\operatorname{DeletedSquare}\left(\operatorname{Ultrafilter}\left(Nat\right)\right)\right)}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/DeletedSquareChromatic.result` (`✓ std3`). ∎

*Resolves.* `Problems/feldman-wilce-bounded-cliques-open-chromatic-strictness` (proved) by `D5/S3/Topology/StoneCech/DeletedSquareChromatic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"feldman-wilce-bounded-cliques-open-chromatic-strictness","declaration_gid":"D5/S3/Topology/StoneCech/DeletedSquareChromatic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

Feldman–Wilce Section 5 Question 2 asks whether the second implication in compact implies finite open chromatic implies bounded cliques is strict. Here X is exactly DeletedSquare (Ultrafilter Nat). Mathlib projectivity of the Stone–Cech compactification of discrete Nat supplies extremal disconnectedness, transported by the existing native ultrafilter homeomorphism. The generic deleted-square power theorem and the countable-power criterion give bounded cliques for every closed orthogonality. The explicit swap graph refutes finite open chromatic number. Hausdorffness is inherited from the actual ambient product.

The construction uses classical choice, with no CH, MA, metrizable-space restriction, common countable base, selector-existence premise, or original open assertion as a hypothesis. The source of the question and of the countable-power criterion is Feldman–Wilce. The deleted-square proof is supplied mathematical input assembled with native clopen separation and Ramsey reuse. No Lean implementation from the author repository is copied: its license is not granted. The primary-source status check is bounded and does not establish global priority or acceptance by the original authors.

## References

- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.BoundedCliqueProperty`
- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.DeletedSquare`
- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.FiniteOpenChromaticProperty`
- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.boundedCliqueProperty_of_countablyCompact_power`
- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.countablyCompactSpace_deletedSquare_power`
- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.no_finite_open_independent_cover`
- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.result`
- Truth anchor: `D5/S3/Topology/StoneCech/DeletedSquareChromatic.swapGraph`
- Dependency: [D5/S3/Combinatorics/GroupWords/NathansonProblem9](../../Combinatorics/GroupWords/NathansonProblem9.md)
- Dependency: [D5/S3/Topology/ExtremallyDisconnected/PointPairSeparation](../ExtremallyDisconnected/PointPairSeparation.md)
- Dependency: [D5/S3/Topology/StoneCech/CountableAvoidance](CountableAvoidance.md)
