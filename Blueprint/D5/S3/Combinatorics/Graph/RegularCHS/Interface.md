# Interface

## Abstract

Complete homogeneous symmetric adjacency coefficients.

**Definition 1.1 (Rooted closed walk counts).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.closedWalks`

*Formalization.* `D5/S3/Combinatorics/Graph/RegularCHS/Interface.closedWalks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For a simple graph G on Fin n and natural length k, closedWalks G k is the natural sum of the diagonal entries of the kth power of its natural adjacency matrix. Length zero is included.

**Definition 1.2 (The even comparison coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq`

*Formalization.* `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For natural n and r, write b(m) for bseq n r m. Then b(0)=1 and b(m+1)=r*(n+2*(m+1)-2)*b(m)/(2*(m+1)) for every natural m. The numerator and denominator are evaluated in the real numbers.

**Theorem 1.3 (The initial comparison coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For all natural n and r, bseq n r 0 equals one.

**Theorem 1.4 (The successor recurrence).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For all natural n, r and m, write b(k) for bseq n r k. The identity is 2*(m+1)*b(m+1)=r*(n+2*(m+1)-2)*b(m), with all scalar arithmetic in the real numbers.

**Theorem 1.5 (The positive-index recurrence).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For natural n, r and m with m at least one, write b(k) for bseq n r k. The identity is 2*m*b(m)=r*(n+2*m-2)*b(m-1). The scalar factors use real arithmetic and the coefficient index m-1 uses natural subtraction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_succ`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.bseq_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Interface.closedWalks`
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/Defs](Defs.md)
