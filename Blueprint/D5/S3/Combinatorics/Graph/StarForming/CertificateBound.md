# Global certificates for two-star formation

## Abstract

For every finite simple graph, disjoint certificates for high internal degree bound the largest inclusion-minimal two-star-forming set by half the sum of the vertex count and dissociation number, rounded down.

The proof is taken from the public note An elementary global certificate bound for 2-star-forming sets, in the-omega-institute/subquorum-colorings, revision 2e430b6481d4959f05f6d805871117261257e39d, docs/STAR_FORMING_CERTIFICATES.md. It applies to every finite simple graph, including the empty graph. Stars and three-vertex paths need not be induced. Minimal always means inclusion-minimal. The established lower comparison beta two at most SF two is attributed to Chellali and Favaron (2009).

**Definition 1.1 (High internal degree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.high`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.high` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For a finite vertex set S, high consists of the vertices s in S with at least two neighbours in S. Adjacency is the original graph adjacency.

**Definition 1.2 (Outside deletion certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.Certificate`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.Certificate` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For vertices s and x, Certificate G S s x means that x is outside S and belongs to no two-leaf star contained in S with s removed and x added. The center is distinct from the leaves and the two leaves are distinct; extra graph edges are permitted.

**Theorem 1.3 (High vertices have outside certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_exists` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For any inclusion-minimal two-star-forming S and every s in high G S, there exists x with Certificate G S s x. Removing s destroys star formation. The resulting obstruction cannot be s itself, because its two neighbours in S already give a path centered at s.

**Theorem 1.4 (One certificate cannot serve two high vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_unique` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every two-star-forming S and high vertices s and t, if x certifies both s and t, then s equals t. A path containing x must contain both s and t; otherwise it survives the corresponding deletion. Its three vertices are exactly x,s,t. The vertex x is adjacent to one of s,t. That high vertex has a selected neighbour different from the other one, producing a path that survives the other deletion.

**Theorem 1.5 (Disjoint certificate sets).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificates_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificates_disjoint` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every two-star-forming S and distinct s,t in high G S, the sets of outside certificates of s and t are disjoint. No bipartition or triangle-free hypothesis is needed.

**Theorem 1.6 (Choose an injective certificate map).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_injection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_injection` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every inclusion-minimal two-star-forming S there exists an injective function from high G S to the complement of S in the whole finite vertex type. This also covers an empty domain.

**Theorem 1.7 (High vertices fit in the complement).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.high_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.high_card_le` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every inclusion-minimal two-star-forming S, the cardinality of high G S is at most the number of vertices outside S.

**Theorem 1.8 (The low part is a dissociation set).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.low_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.low_independent` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every S, the set S minus high G S is two-independent in the original IsKIndependent definition. Every retained vertex already had fewer than two neighbours in S, and deleting vertices cannot increase that count.

**Theorem 1.9 (The global cardinality inequality).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.minimal_card_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.minimal_card_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every inclusion-minimal two-star-forming S, twice its cardinality is at most the cardinality of the vertex type plus beta G 2. The complement bounds the high part, and beta bounds the low part.

**Theorem 1.10 (The floor bound for each minimal set).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.minimal_card_le_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.minimal_card_le_floor` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every inclusion-minimal two-star-forming S, its cardinality is at most the natural-number quotient of the vertex count plus beta G 2 by two. This quotient is the floor in the source statement.

**Theorem 1.11 (The upper two-star-forming number).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.sf_le_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.sf_le_floor` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (the note has no named byline) (2026). *An elementary global certificate bound for 2-star-forming sets*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/2e430b6481d4959f05f6d805871117261257e39d/docs/STAR_FORMING_CERTIFICATES.md>.

*Commentary.*

For every finite simple graph with decidable equality and adjacency, SF G 2 is at most the floor of the vertex count plus beta G 2, divided by two. The finite supremum ranges over the existing inclusion-minimal star-forming predicate. Injectivity does not show that replacing high vertices by certificates preserves dissociation: inserted vertices may create new paths. No equality of SF and beta is inferred.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.Certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_exists`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_injection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificate_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.certificates_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.high`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.high_card_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.low_independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.minimal_card_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.minimal_card_le_floor`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CertificateBound.sf_le_floor`
- Dependency: [D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation](../StarFormingDissociationRefutation.md)
