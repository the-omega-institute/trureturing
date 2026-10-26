# Complete multipartite CHS norm extrema

## Abstract

The complete multipartite branch of the cited article's CHS norm problem.

**Definition 1.1 (Complete homogeneous spectral value).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chs`

*Formalization.* `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For a complete multipartite adjacency matrix, chs is the complete homogeneous symmetric polynomial evaluated at its real eigenvalues. This is the spectral quantity in the cited article's norm definition in Section 1.1 and Theorem 1.4.

**Definition 1.2 (Complete homogeneous spectral norm).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chsNorm`

*Formalization.* `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chsNorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

chsNorm is the real power of chs with exponent the reciprocal of the natural degree. For an even degree 2m this is the CHS norm used in the cited article's Section 1.1 definition.

**Definition 1.3 (Fixed-part-count multipartite extremum claim).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For r at least two, n at least r, and m at least one, positive part sizes summing to n have their CHS 2m-norm minimized by the concentrated part multiset and maximized by the balanced part multiset. Equality at either endpoint forces equality of part multisets up to permutation.

**Theorem 1.4 (Complete multipartite branch of Problem 3).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/chavez-2023-multipartite-chs-norm-extrema` (proved) by `D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chavez-2023-multipartite-chs-norm-extrema","declaration_gid":"D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every r at least two, n at least r, and m at least one, and every positive part-size vector of total n, the CHS 2m-norm is at least the value at the part sizes n minus r plus one followed by r minus one singletons. Equality forces the same part multiset. The norm is at most the value at the balanced part sizes, and equality likewise forces the balanced multiset.

The proof uses the spectral identity chs a d = recH a d, the reciprocal recurrence, and strict coefficient comparison under two-part transfers. Positivity of the even coefficients permits the real-power inequalities and their equality converses.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chs`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chsNorm`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result`
- Dependency: [D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal](Extremal.md)
- Dependency: [D5/S3/Combinatorics/Graph/MultipartiteCHS/Spectral](Spectral.md)
