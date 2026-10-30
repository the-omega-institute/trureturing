# The cycle comparison bound

## Abstract

Even complete homogeneous coefficients of cycle adjacency spectra.

**Theorem 1.1 (Cycle coefficients are bounded by the comparison sequence).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/CycleBound.chs_cycle_le_bseq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/CycleBound.chs_cycle_le_bseq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every n at least three and every natural m, the complete homogeneous symmetric polynomial of degree 2m evaluated at the adjacency eigenvalues of the cycle on n vertices is at most bseq(n,4,m). The comparison sequence starts at one and satisfies (2m+2)bseq(n,4,m+1)=4(n+2m)bseq(n,4,m). The inequality includes m=0.

The argument applies to every simple graph of maximum degree at most two. Its real adjacency eigenvalues have sum zero and absolute value at most two, by the trace identity and the row sum bound in Gershgorin's theorem. The reciprocal product identity from the path coefficient module identifies the complete homogeneous coefficients with those of H(t)=product_i(1-a_i t)^(-1).

Every even coefficient of a reciprocal product with real parameters is nonnegative. For parameters of one sign this follows directly, after changing t to -t when needed. For opposite signs a>0>b, the identity (a-b)g_a(t)g_b(t)=a g_a(t)-b g_b(t), where g_a(t)=(1-at)^(-1), reduces the assertion to two products with one fewer factor and positive weights.

Formal differentiation gives (1-4t^2)H'(t)=4ntH(t)-t sum_i(4-a_i^2)H(t)g_(a_i)(t). Each summand has nonnegative even coefficients, including the repeated factor g_(a_i). Taking the coefficient of t^(2m+1) gives (2m+2)h_(2m+2) at most 4(n+2m)h_(2m). Induction against the defining comparison recurrence proves the bound. The cycle specialization uses its exact degree two; no connectedness assumption is used for the intermediate bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/CycleBound.chs_cycle_le_bseq`
- Dependency: [D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm](../PathCHS/PathCHSNormClosedForm.md)
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/Newton](Newton.md)
