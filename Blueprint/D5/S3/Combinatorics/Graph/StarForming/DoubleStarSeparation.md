# A six-vertex separation for the coloring comparison

## Abstract

The six-vertex double star has dissociation number four, upper two-star-forming number four and sub-quorum color maximum five. It disproves the proposed coloring comparison on both bipartite and triangle-free graphs.

The source is the complete public note An elementary global certificate bound for 2-star-forming sets, the-omega-institute/subquorum-colorings at revision 2e430b6481d4959f05f6d805871117261257e39d, docs/STAR_FORMING_CERTIFICATES.md. The graph and all three parameters below are exactly those in its double-star example.

**Definition 1.1 (The adjacent centers and four leaves).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The vertex type is Fin 6. Centers 0 and 1 are adjacent, leaves 2 and 3 attach to 0, and leaves 4 and 5 attach to 1. There are no other edges. This is the six-vertex double star, distinct from the seven-slot construction that attaches a double star to a base vertex.

**Theorem 1.2 (Dissociation number four).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.beta_doubleStar`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.beta_doubleStar` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The existing beta doubleStar 2 equals four. The four leaves are an independent set. Every set with at least five vertices contains a selected center with at least two selected neighbours.

**Theorem 1.3 (Upper two-star-forming number four).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.sf_doubleStar`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.sf_doubleStar` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The existing SF doubleStar 2 equals four. The four leaves form an inclusion-minimal star-forming set: each outside center sees two leaves, while deleting a leaf leaves that vertex on no path when added back. Every five-set contains a star-forming four-set. If the missing vertex is a center, delete the other center. If the missing vertex is a leaf, delete the opposite center. The full vertex set also contains the four leaves and is not minimal. The finite subset proof uses the existing LocalTwo equivalence.

**Theorem 1.4 (Sub-quorum maximum five).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.psiSq_doubleStar`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.psiSq_doubleStar` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The existing psiSq doubleStar equals five, counting actual represented colors on a partial support. Give both centers one color and give the four leaves four distinct further colors. Six represented colors would force all six vertices to be colored injectively. Then a center has three differently colored neighbors, so its single same-color closed-neighborhood vertex cannot form half of its four colored closed-neighborhood vertices.

**Theorem 1.5 (A proper two-coloring).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar_bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar_bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The double star admits a proper coloring with Fin 2. One side contains 0,4,5 and the other contains 1,2,3.

**Theorem 1.6 (No triangle).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar_triangleFree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar_triangleFree` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The double star is clique-free at three, as follows from its proper two-coloring.

**Theorem 1.7 (The complete strict separation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.exact_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.exact_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The simultaneous equalities are beta doubleStar 2 equals four, SF doubleStar 2 equals four, and psiSq doubleStar equals five. In particular SF doubleStar 2 is strictly less than psiSq doubleStar.

**Definition 1.8 (The two proposed graph-class comparisons).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The claim is the disjunction of the universal comparison psiSq G at most SF G 2 on every finite bipartite graph, and the same universal comparison on every finite triangle-free graph. Refuting this disjunction refutes each comparison.

**Theorem 1.9 (Both larger graph classes fail the comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

The six-vertex double star belongs to both classes and has five greater than four, so neither class satisfies the proposed universal inequality. A rectangular-grid comparison still requires a separate proof. No all-grid equality, universal five-sixths theorem, or claim of worldwide novelty or priority follows from this example.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.beta_doubleStar`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar_bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.doubleStar_triangleFree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.exact_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.psiSq_doubleStar`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.sf_doubleStar`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CertificateBound](CertificateBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Semantics](Semantics.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/ColoringBounds](../SubQuorum/ColoringBounds.md)
