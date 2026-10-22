# Defs

## Abstract

Complete homogeneous symmetric adjacency coefficients.

**Theorem 1.1 (Real adjacency matrices are Hermitian).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.adjMatrix_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Defs.adjMatrix_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every natural n and simple graph G on Fin n, the real adjacency matrix is Hermitian. Symmetry of graph adjacency supplies the matrix symmetry.

**Definition 1.2 (Adjacency complete homogeneous coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.chs`

*Formalization.* `D5/S3/Combinatorics/Graph/RegularCHS/Defs.chs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every graph G on Fin n and natural degree d, chs G d is the complete homogeneous symmetric polynomial hsymm of degree d evaluated at the real eigenvalues of the adjacency matrix.

**Definition 1.3 (Adjacency CHS norms).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.chsNorm`

*Formalization.* `D5/S3/Combinatorics/Graph/RegularCHS/Defs.chsNorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every graph G and natural degree d, chsNorm G d is the real power of chs G d with exponent one divided by d. The extremal claim uses only positive even degrees.

**Definition 1.4 (Extrema over connected regular graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/RegularCHS/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every n at least three and m at least one, both the cycle and the complete graph on Fin n are connected and regular, and every connected regular graph G on Fin n has its degree 2m CHS norm between those of the cycle and the complete graph. The word connected has the usual graph theoretic meaning.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.adjMatrix_isHermitian`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.chs`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.chsNorm`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Defs.claim`
