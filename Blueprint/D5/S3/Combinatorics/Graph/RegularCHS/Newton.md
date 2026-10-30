# Newton

## Abstract

Complete homogeneous symmetric adjacency coefficients.

**Theorem 1.1 (Nonnegative comparison coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For all natural n, r and m, bseq n r m is nonnegative. The recursion has nonnegative factors and a positive denominator.

**Theorem 1.2 (Monotonicity in the degree parameter).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For natural n and r with r at least four, and every natural m, bseq n 4 m is at most bseq n r m.

**Theorem 1.3 (Traces and natural walk counts).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.trace_pow_eq_closedWalks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.trace_pow_eq_closedWalks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every simple graph G on Fin n and every natural k, the trace of the kth power of the real adjacency matrix equals the real coercion of closedWalks G k. The natural-to-real ring homomorphism commutes with matrix powers.

**Theorem 1.4 (Spectral moments count walks).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.sum_eigenvalues_pow_eq_closedWalks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.sum_eigenvalues_pow_eq_closedWalks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every simple graph G on Fin n and every natural k, the sum of the kth powers of its real adjacency eigenvalues equals the real coercion of closedWalks G k. Unitary diagonalization preserves the trace.

**Theorem 1.5 (The complete homogeneous Newton recurrence).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.hsymm_newton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.hsymm_newton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every finite decidable type of indices, every real family a and every natural d, d plus one times the complete homogeneous symmetric value at degree d plus one equals the sum over k from zero through d of the power sum of degree k plus one times the complete homogeneous value of degree d minus k. The reciprocal linear-factor product identifies the generating series, and formal differentiation gives the recurrence.

**Theorem 1.6 (The graph Newton recurrence).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_newton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_newton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every simple graph G on Fin n and every natural d, d plus one times chs G at d plus one equals the sum over k from zero through d of closedWalks G at k plus one times chs G at d minus k. Walk counts are coerced to the real numbers.

**Theorem 1.7 (Nonnegative adjacency coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every simple graph G on Fin n and every natural d, chs G d is nonnegative. Strong induction uses nonnegative closed walk counts in the Newton recurrence. Odd degrees are included.

**Theorem 1.8 (Closed walk domination implies coefficient domination).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_le_of_closedWalks_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_le_of_closedWalks_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

Let F and G be simple graphs on the same Fin n. If closedWalks F k is at most closedWalks G k for every positive natural k, then chs F d is at most chs G d for every natural d. The induction combines both moment domination and nonnegativity of earlier coefficients.

**Theorem 1.9 (The complete graph upper bound).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_le_top`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_le_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every simple graph G on Fin n and every natural d, chs G d is at most the coefficient of degree d of the complete graph on Fin n. Entrywise adjacency domination is preserved by powers of nonnegative matrices.

**Theorem 1.10 (Nonnegativity in even degree).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_two_mul_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_two_mul_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every simple graph G on Fin n and every natural m, chs G at degree 2m is nonnegative. No strict positivity or edge assumption is asserted here.

**Theorem 1.11 (The even Newton convolution for the comparison sequence).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For all natural n, r and m, 2m times bseq n r m equals n times the sum over j less than m of r to the power j plus one times bseq n r at m minus one minus j. All coefficient arithmetic is real. The defining first-order recurrence telescopes to this convolution.

**Theorem 1.12 (Even moment lower bounds imply coefficient lower bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_ge_bseq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_ge_bseq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every graph G on Fin n, natural parameter r and natural m, if n times r to the power j is at most closedWalks G at length 2j for every positive j, then bseq n r m is at most chs G at degree 2m. Select the even moments from the Newton recurrence, discard nonnegative remaining terms, and apply induction to the earlier even coefficients. No additional minimum degree premise is needed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_convolution`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_mono`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.bseq_nonneg`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_ge_bseq`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_le_of_closedWalks_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_le_top`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_newton`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_nonneg`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.chs_two_mul_pos`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.hsymm_newton`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.sum_eigenvalues_pow_eq_closedWalks`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/Newton.trace_pow_eq_closedWalks`
- Dependency: [D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm](../PathCHS/PathCHSNormClosedForm.md)
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/Interface](Interface.md)
