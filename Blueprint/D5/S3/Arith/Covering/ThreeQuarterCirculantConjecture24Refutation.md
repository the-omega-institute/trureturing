# The Boundary of Conjecture 2.4

## Abstract

Conjecture 2.4's literal positive-integer quantifier conflicts with its degree-two graph convention at k equal to one.

**Definition 1.1 (The literal source claim).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.claim`

*Formalization.* `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.claim` (`✓ std3`).

*Citation.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

For every k at least one, the proposed order, two lattice columns, full radius-k coverage, exact-radius witness, and two-element outgoing neighbor set all hold simultaneously. The final clause is the source's degree-two digraph requirement with arcs treated as a set.

**Theorem 1.2 (The one-neighbor boundary retains its sector and lattice properties).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.boundary_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.boundary_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

At k=1 the order is three, both steps are residue one, and each vertex has one distinct outgoing neighbor. Radius-one sector coverage, the exact-radius witness, and the lattice kernel identity still hold.

**Theorem 1.3 (The degree-two assertion fails at k equal to one).**

Lean statement: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/dalfo-fiol-reyes-three-quarter-conjecture-24` (refuted) by `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dalfo-fiol-reyes-three-quarter-conjecture-24","declaration_gid":"D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Dalfo and M. A. Fiol and M. A. Reyes (2026). *A note on three-quarters circulant digraphs*. DOI: [10.61091/um128-09](https://doi.org/10.61091/um128-09). URL: <https://arxiv.org/html/2609.33718v1>.

*Commentary.*

At k=1 the order is three and both proposed steps are residue one. Every vertex therefore has one distinct outgoing neighbor. This refutes the literal degree-two graph assertion; it does not refute the sector-distance or lattice clauses, which hold at k=1.

## References

- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.boundary_facts`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.claim`
- Truth anchor: `D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation.result`
- Dependency: [D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture](ThreeQuarterCirculantConjecture.md)
