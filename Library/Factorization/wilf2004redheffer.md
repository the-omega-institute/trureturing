---
bibkey: wilf2004redheffer
authors: Herbert S. Wilf
year: 2004
title: The Redheffer matrix of a partially ordered set
doi: 10.48550/arXiv.math/0408263
claim: "Theorem 1 characterizes the contributing permutations of the Redheffer matrix by a division-chain cycle through 1, with all other elements fixed, and counts them by ordered factorizations."
strata_touched:
  - D5/S3/Arith/GranvikRedhefferSupport
license: citation-only
triage: anchor
---

# Division-chain cycles in the Redheffer matrix

Wilf defines `R_n(i,j)=1` when `i` divides `j` or `j=1`. Section 2 and
Theorem 1 describe the nonidentity contributing permutations: their unique
nontrivial cycle contains 1 and follows an increasing division chain before
returning to 1; all other elements are fixed. The identity is the separate
empty-factorization contribution. The theorem evaluates the permanent by
counting ordered factorizations. Section 3 extends the argument to finite
partially ordered sets with a least element.

For the modified matrix with `(n,n)` set to zero, a contributing permutation
must move `n`; the division-chain description therefore places `n` at the
end of the cycle through 1. This specializes the setting relevant to
A145110. Wilf's stated count is a count of permutations, not a count of the
union of their matrix positions, and the paper does not state the A145110
support-count formula.

## Verified locator

- Declared DOI: 10.48550/arXiv.math/0408263
- DOI URL: https://doi.org/10.48550/arXiv.math/0408263
- Versioned abstract: https://arxiv.org/abs/math/0408263v1
- Versioned source: https://arxiv.org/src/math/0408263v1
- The arXiv abstract and TeX source identify Herbert S. Wilf, the title
  above, and submission version 1. The source's first theorem is the
  ordered-factorization and division-chain result described here.

The arXiv page links its assumed-license notice. This note supplies a
bibliographic locator and mathematical description and asserts no license
to redistribute the paper.
