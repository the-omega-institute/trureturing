# The cyclic order spectrum

## Abstract

The regular cyclic bag counts have exactly a clique-packet branch and a period-three full-support branch.

**Theorem 1.1 (The exact spectrum of bounded cyclic counts).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKaySpectrum.cyclic_order_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RegularInduced/DysonMcKaySpectrum.cyclic_order_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

Let r be at least four and q be positive. For cyclic positions i, choose nonnegative counts x_i at most s, of total m, satisfying x_{i-1}+x_i+x_{i+1} = q at every occupied position. Such counts exist exactly in either of two cases. In the packet case, m = kq for a nonnegative integer k, with 2k at most r; if q exceeds s then 3k is at most r, and if q exceeds 2s then k = 0. Packets occupy one bag when q is at most s, or two consecutive bags when q is at most 2s, with empty bags separating them. In the full-support case, 3m = rq, q is between three and 3s, and three divides r or q. Subtracting consecutive regularity equations forces the occupied counts to have period three. Positive triples summing to q give the full-support selections when three divides r; constant counts give them when three divides q. The packet branch includes the empty selection.

## References

- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKaySpectrum.cyclic_order_spectrum`
