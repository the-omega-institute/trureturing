# Actual subsets and five-column minimal domination

## Abstract

Actual inclusion-minimal dominating subsets of the labelled open three-row grid admit an exact column-word encoding and a five-column private-witness criterion.

**Definition 1.1 (Inclusion minimality).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.MinimalDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.MinimalDominating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Domination uses SimpleGraph.IsDominating and is required separately. Every proper finite subset must fail domination. No minimum-cardinality, total-domination, independence or symmetry condition is added.

**Definition 1.2 (Closed neighbourhoods).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.Closed`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.Closed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Closed G u v means u=v or G.Adj u v.

**Definition 1.3 (Existential private witnesses).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ClosedPrivate`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ClosedPrivate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ClosedPrivate G S v z means z is closed-adjacent to v and every selected closed neighbour of z equals v. Witnesses are propositions and are never counted choices.

**Theorem 1.4 (Private-witness characterization).**

$$\forall (V : Type), (\operatorname{Finite}\left(V\right)) \Rightarrow (\forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), (\operatorname{MinimalDominating}\left(G, S\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(G, S\right)) \land (\forall (v : V), (v \in S) \Rightarrow (\exists (z : V), \operatorname{ClosedPrivate}\left(G, S, v, z\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimal_iff_closed_private` (`✓ std3`). ∎

*Citation.* Silvere Gangloff; Alexandre Talon (2019). *Asymptotic growth rate of square grids dominating sets: a symbolic dynamics approach*. DOI: [10.48550/arXiv.1906.10779](https://doi.org/10.48550/arXiv.1906.10779). URL: <https://arxiv.org/abs/1906.10779>.

*Commentary.*

The proof uses the existing criticalVertices, privateNeighbors and selfCritical_no_selected_neighbor suppliers. The isolated-or-outside-private-neighbour characterization, under the domination premise, is published as Proposition 1 of Gangloff and Talon, arXiv:1906.10779v2, https://arxiv.org/abs/1906.10779. No novelty is claimed for that characterization. No external prose or proof code is transplanted.

**Definition 1.5 (The ordinary open grid).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.grid`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.grid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertices are Fin 3 × Fin n; (r,c) represents the source label (r+1,c+1). Adjacency is exactly Nat.dist r s + Nat.dist c d = 1. The finite column type supplies open ends.

**Definition 1.6 (Read the masks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.encode`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each column mask has one Boolean bit for each of the three labelled rows. The bit is true exactly when the actual vertex belongs to the subset.

**Definition 1.7 (Recover the subset).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.decode`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoded subset contains precisely the vertices whose column-mask bit is true.

**Theorem 1.8 (Selected bits).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.mem_decode`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.mem_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n, word w and vertex v, membership v ∈ decode w is equivalent to w(v.column)(v.row)=true.

**Definition 1.9 (One subset, one word).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.subsetWordEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.subsetWordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finset (Vertex n) and Word n are equivalent through mutually inverse encode and decode. No automorphisms or witness choices are identified.

**Definition 1.10 (Real empty versus absent).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.padded`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.padded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A signed column in 0 ≤ c < n returns some mask; other coordinates return none. The present all-false mask differs from absence.

**Definition 1.11 (The original family).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimalSets`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimalSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter every actual labelled vertex subset by MinimalDominating (grid n). The original family is defined before transport to words.

**Definition 1.12 (The source count).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.actualCount`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.actualCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

actualCount n is the cardinality of minimalSets n. The requested generating series uses positive n and separately sets its constant coefficient to zero.

**Definition 1.13 (Acceptance against the actual graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ValidWord`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ValidWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Acceptance means domination of decode w and an existential closed private witness for each selected vertex.

**Theorem 1.14 (Exact acceptance).**

$$\forall (n : \mathbb{N}), \forall (w : \operatorname{Word}\left(n\right)), (\operatorname{ValidWord}\left(w\right)) \Leftrightarrow (\operatorname{MinimalDominating}\left(\operatorname{grid}\left(n\right), \operatorname{decode}\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.validWord_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the general characterization to the independently defined actual decoded subset.

**Definition 1.15 (Restrict the bijection).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimalWordEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimalWordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict subsetWordEquiv to the actual minimal dominating subsets and accepted words.

**Definition 1.16 (Five-column criterion).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ColumnTest`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ColumnTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every centre vertex is closed-dominated. Every selected centre vertex has an actual closed-neighbour witness; uniqueness is tested among selected vertices at column distance at most two. Actual finite-grid vertex types exclude absent witnesses.

**Theorem 1.17 (Every real centre at every width).**

$$\forall (n : \mathbb{N}), \forall (S : \operatorname{Finset}\left(\operatorname{Vertex}\left(n\right)\right)), (\operatorname{MinimalDominating}\left(\operatorname{grid}\left(n\right), S\right)) \Leftrightarrow (\forall (c : \operatorname{Fin}\left(n\right)), \operatorname{ColumnTest}\left(S, c\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimal_iff_column_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A witness is at column distance at most one, and every selected neighbour of it is at distance at most two by the natural-distance triangle inequality. This proves that the five-column restriction retains the complete proper-subset condition, including widths one and two.

The actual subset family is the source of the count throughout the transfer construction. The column criterion supplies the local tests, and the subset-word equivalence preserves every labelled choice without counting existential witnesses.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.Closed`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ClosedPrivate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ColumnTest`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.MinimalDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.ValidWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.actualCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.decode`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.encode`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.grid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.mem_decode`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimalSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimalWordEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimal_iff_closed_private`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.minimal_iff_column_tests`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.padded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.subsetWordEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.validWord_iff`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem](../DominatingSetAverageBoundNonstem.md)
