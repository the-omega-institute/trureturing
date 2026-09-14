---
bibkey: lagarias2004li
authors: Jeffrey C. Lagarias
year: 2004
title: Li Coefficients for Automorphic L-Functions
doi: null
url: https://arxiv.org/abs/math/0404394v4
claim: The multiplicity-weighted Li sum over actual nontrivial Riemann zeta zeros converges under zero-modulus cutoffs.
strata_touched:
  - D5/S3/Weil/ZeroData/LiZeroSumConvergence
license: bibliographic-reference-only
triage: anchor
---
<!-- GID: D5/L/Weil/lagarias2004li -->
# Li Zero-Sum Convergence

## Verified locator

https://arxiv.org/abs/math/0404394v4

Lagarias, arXiv:math/0404394v4, Introduction, equation (1.1), printed page 1,
defines the Li expression as the sum of `1-(1-1/rho)^n` over the actual
nontrivial Riemann zeta zeros counted with multiplicity. The prime on the
sum means the limit of the finite sums over `|rho| <= T`. The accompanying
paragraph states convergence for positive and negative integer indices;
the present formalization treats natural indices, including zero. The
first submission is dated 2004; the cited fourth version is dated
4 May 2005 and its title page says 11 April 2005.

The height convention is stated separately in Masatoshi Suzuki,
*Li coefficients as norms of functions in a model space*,
https://arxiv.org/abs/2301.05779v2, Introduction, equation (1.1) and its
following paragraph: take the limit over `|Im rho| <= T`, retaining
multiplicities. The retained versioned HTML has a 14 June 2023 watermark
and a displayed date of 24 August 2026; this bibliographic discrepancy
does not alter the quoted summation convention.

The Lean theorems use the repository's exhaustive, injective `ZeroData`
presentations of actual zeta zeros and their exact analytic multiplicities.
They prove absolute summability of the real parts and convergence of three
conjugation-invariant finite sums: spectral radius, height, and zero modulus.
The spectral parameter is `gamma=-i*(rho-1/2)`; the opposite sign convention
in the source has the same norm. Strict-strip geometry proves that the
height and radial filters of the spectral ball of radius `T+1` have exactly
their stated memberships for every real `T`.

The proof of the real estimate is local to this formalization. Writing
`u=1/rho`, it uses `|Re u| <= |u|^2` and a joint power induction to obtain
`|1-Re((1-u)^n)| <= (2^n-1)*|u|^2` on the tail. The reciprocal-square
zero weight is supplied by the existing zeta summability theorem. For
`|gamma| >= 2`, the majorant is `4*2^n*m/(1+|gamma|^2)`. Every term outside
that tail is retained in a finite exceptional set. This constant is only
a convergence estimate and has no role as Li's fixed first coefficient.

The identification with the derivative definition in Lagarias equation
(1.3), and the resulting positivity equivalence, are separate obligations.
No derivative identity, Riemann hypothesis, or probability representation
is a hypothesis of these convergence results. No assertion of absolute
summability of the unpaired complex terms is made.

The cited passages were read from retained versioned primary-source
excerpts. Li's 1997 publisher endpoint supplied metadata but not the full
article; its PDF request returned HTTP 406. No original Li theorem or
proof is attributed to that inaccessible text here. This note paraphrases
mathematical statements and copies no third-party proof code.
