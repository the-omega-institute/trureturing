---
bibkey: suvagiya2026parity
authors: Vaibhav Suvagiya
year: 2026
title: "Parity families and signed spectra: kernel averaging, near-Ramanujan bounds, and exact circulant models"
doi: 10.48550/arXiv.2607.17343
url: https://arxiv.org/html/2607.17343v2
claim: "Conjecture 28 asserts that for every integer m >= 4 the minimum spectral radius over all edge signings of C_(8m)(1,2) is the largest real root of x^4-2x^3-6x^2+12x-4."
strata_touched:
  - D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation
license: citation-only
triage: anchor
---

# Suvagiya's period-eight global optimality conjecture

## Verified locator

DOI: 10.48550/arXiv.2607.17343

URL: https://arxiv.org/html/2607.17343v2

The source is arXiv:2607.17343v2, section 12.3, Conjecture 28. The withdrawn
companion arXiv:2607.18334 is not the source of this assertion.

## Statement and conventions

Conjecture 28, titled "Period-8 global optimality", states:

> For every integer m >= 4, min_sigma rho(A_sigma) = r_* on C_(8m)(1,2),
> where r_* is the largest real root of x^4 - 2x^3 - 6x^2 + 12x - 4 = 0.

The vertices of C_n(1,2) are the residues modulo n. Its undirected edges are
{i,i+1} and {i,i+2}; every edge has its own independent sign in {−1,+1}.
The adjacency matrix is real and symmetric. Its spectral radius is the
maximum absolute value of its eigenvalues. The signings include both possible
products of the signs around the Hamilton cycle. Theorem 26 gives an upper
bound from a particular periodic family; it does not prove the unrestricted
lower bound in Conjecture 28.

## Exact counterexample

Take n = 32. Put a_i = +1 for 0 <= i < 31 and a_31 = −1 on {i,i+1}.
For {i,i+2}, repeat (1,1,−1,1,−1,−1,1,−1) four times, then replace
b_30 by −1 and b_31 by +1. In particular, the three seam edges have weights
A_31,0 = −1, A_30,0 = −1, and A_31,1 = +1. The matrix has zero diagonal,
64 undirected edges, four nonzero entries per row, and Hamilton sign product −1.

The squared adjacency is annihilated by

R(y) = y^8−32y^7+416y^6−2816y^5+10568y^4−21632y^3+22168y^2−9408y+1262.

The eight exact finite Horner identities give R(A^2) = 0. All nine
coefficients of R((279/100)^2+z) are positive; the constant is
6810961358286782272485104951163521/10^32. Spectral mapping shows that
R(lambda^2) = 0 for each real eigenvalue lambda. Since R(y) is positive
for y >= (279/100)^2, every absolute eigenvalue is bounded by 279/100.
The maximum absolute eigenvalue therefore is at most 279/100.
For f(x) = x^4−2x^3−6x^2+12x−4,

f(279/100) = −6766519/100000000 < 0, while f(3) = 5 > 0.

There is a real root strictly between 279/100 and 3. The greatest real root
is at least that root, so the exhibited signing has spectral radius strictly
less than the conjectured minimum. This refutes the universal assertion by
its instance m = 4.

## Scope

The unrestricted lower bound is false. Theorem 26's upper bound is unaffected.
The exact optimum at n = 32, the optima at other sizes, and any repaired
restriction on the class of signings remain undetermined by this result.

The bounded source and literature screen recorded in issue 11744 found the
current author version still presenting Conjecture 28 as open. That screen
does not assert exhaustive literature coverage or publication priority.
