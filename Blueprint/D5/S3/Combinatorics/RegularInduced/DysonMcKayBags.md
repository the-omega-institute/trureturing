# The order spectrum of a cycle-clique union

## Abstract

A regular induced union is characterized by component orders chosen at a single common degree.

**Theorem 1.1 (Adding component spectra at one degree).**

Lean statement: `D5/S3/Combinatorics/RegularInduced/DysonMcKayBags.regular_union_order_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RegularInduced/DysonMcKayBags.regular_union_order_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul W. Dyson, Brendan D. McKay (2026). *Ramsey numbers for regular induced subgraphs*. DOI: [10.48550/arXiv.2604.08215](https://doi.org/10.48550/arXiv.2604.08215). URL: <https://arxiv.org/abs/2604.08215v3>.

*Commentary.*

For a finite list of components (r_i,s_i) with r_i at least three and s_i at least one, a regular induced subgraph of order p exists exactly when there is a positive integer q and component orders m_i summing to p with the following properties. The common degree is q-1. For r_i = 3, the component is a clique and its selected order is either zero or q, with q at most 3s_i in the latter case. For r_i at least four, either m_i = k_i q with 2k_i at most r_i, with 3k_i at most r_i if q exceeds s_i, and with k_i = 0 if q exceeds 2s_i; or 3m_i = r_i q with q between three and 3s_i and with three dividing r_i or q. Counting selected vertices in each bag gives the forward direction. Conversely, each bounded bag count is realized by selecting that many distinct clique vertices, and the cyclic regularity equations give degree q-1 throughout the selected union. Empty component selections and p = 0 are included.

## References

- Truth anchor: `D5/S3/Combinatorics/RegularInduced/DysonMcKayBags.regular_union_order_spectrum`
- Dependency: [D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs](DysonMcKayDefs.md)
- Dependency: [D5/S3/Combinatorics/RegularInduced/DysonMcKaySpectrum](DysonMcKaySpectrum.md)
