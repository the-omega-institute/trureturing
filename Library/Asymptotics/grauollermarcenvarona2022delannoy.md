---
bibkey: grauollermarcenvarona2022delannoy
authors: J. M. Grau, A. M. Oller-Marcén and J. L. Varona
year: 2022
title: A class of weighted Delannoy numbers
doi: 10.48550/arXiv.2501.09726
url: https://arxiv.org/abs/2501.09726v2
claim: "Section 6 conjectures additive-error diagonal ratio limits for the factorial and n^n borders with all three recurrence coefficients equal to one."
strata_touched:
  - D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaFactorialBorderGrowth
  - D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaPowerBorderGrowth
license: citation-only
triage: anchor
---

# Superexponential borders of weighted Delannoy arrays

## Verified locator

DOI: 10.48550/arXiv.2501.09726

Source: https://arxiv.org/abs/2501.09726v2

The pinned arXiv version is v2. The journal reference is *Filomat*
36(17) (2022), 5985–6007. Section 6, “Further work”, arXiv page 18,
contains the following sentences:

> This happens, for instance, if α = β = γ = 1 and f_{n,0} = f_{0,n} = n!. In this example [19, OEIS A346374] we conjecture that f_{n+1,n+1}/f_{n,n} ≈ n + 1 (where a_n ≈ b_n means, as usual, that a_n − b_n → 0 when n → ∞). The same phenomenon happens if f_{n,0} = f_{0,n} = n^n, with our conjecture now being f_{n+1,n+1}/f_{n,n} ≈ e · (n + 1/2) [20, OEIS A346385].

## Mathematical correspondence

The natural array `f b` has borders `f b 0 n = b n` and
`f b (m + 1) 0 = b (m + 1)`. Its interior recursion is
`f b (m + 1) (n + 1) = f b m (n + 1) + f b (m + 1) n + f b m n`.
Thus it is exactly the source array at α = β = γ = 1. The origin is
`b 0`, and both selected borders have value one there, including `0^0 = 1`.
Each claim casts the diagonal entries to the reals and interprets “≈” as
convergence of the difference to zero. The ratio uses real division.

The factorial module proves `claimFactorial`; the power module proves
`claimPower`. Their results concern every natural index asymptotically.
The common proof uses the exact border convolution, summable factorial
majorants and first-order dominated convergence. The stronger second-order
expansions and explicit error rates are not asserted by these results.

Literature completeness is `ASSUMED-UNVERIFIED`.
