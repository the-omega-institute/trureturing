# Original masked nondegenerate hypermatrix count

## Abstract

Original masked nondegenerate hypermatrix count

**Theorem 1.1 (Original masked nondegenerate hypermatrix count).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/koprowski-lewis-2026-conjecture-3-1-hypermatrix-count` (proved) by `D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"koprowski-lewis-2026-conjecture-3-1-hypermatrix-count","declaration_gid":"D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Acknowledgement.* Christine Berkesch Zamaere, Daniel Erman, Manoj Kummini, Steven V. Sam (2013). *Tensor complexes: Multilinear free resolutions constructed from higher tensors*. DOI: [10.4171/JEMS/421](https://doi.org/10.4171/JEMS/421). URL: <https://arxiv.org/abs/1101.4604v5>.

*Commentary.*

Let F be any finite field, q its cardinality, and k any natural number at least one. Let lambda,mu map Fin(k) to natural numbers and be antitone. For every j assume mu(j) at most lambda(j), lambda(j) at most k minus j, and mu(j) strictly less than k minus j. Count the actual pairs of (k plus one)-by-k matrices over F whose first face vanishes in rows r at least k plus one minus lambda(j), whose second face vanishes in rows r at least k plus one minus mu(j), and whose evaluated integral coefficientPolynomial is nonzero. The count is q to k squared times (q minus one) to 2k times the product over j of [k plus one minus j minus lambda(j)]_q times [k minus j minus mu(j)]_q. The determinant is evaluated on the same tensor entries. Its rank equivalence is internal: every nonzero face combination over the algebraic closure has rank k exactly when this determinant is nonzero. The proof connects these actual objects to the constructed masked-cell count and factors the actual weighted sum. It retains k=1 and every characteristic, including characteristic two; no rational-combination restriction or normalization assumption is added.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount.result`
- Dependency: [D5/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction](MaskedTensorWeightedReduction.md)
