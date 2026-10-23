---
bibkey: zhang2020variational
authors: Haonan Zhang
year: 2020
title: From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture
doi: null
url: https://arxiv.org/abs/1811.01205v2
claim: Trace powers of matrix products admit explicit variational minimum and maximum formulas via Schatten Holder and Young inequalities.
strata_touched:
  - D5/S3/Quantum/Hiai
license: citation-only
triage: anchor
---

# Inverse-mean variational formula

Theorem 3.3, formula (3.2), gives a maximum formula for trace powers of matrix
products with positive exponents whose reciprocals add. Its proof uses
Schatten Holder, scalar Young and an explicit polar-decomposition optimizer.

For positive definite X and M and r > 0, write R = X M inverse X.
The retained concrete formula bounds
2 Tr((Z* X squared Z) to exponent r/2) - Tr((Z* M Z) to exponent r)
by Tr(R to exponent r), for every complex Z. Equality is attained by
Z = M inverse X. This optimizer is invertible and generally nonselfadjoint.
The proof factors XZ as X M to exponent minus one half times
M to exponent one half Z; row and column Gram trace identities preserve
the adjoints. No commutativity hypothesis is used.

This classical variational result is a supplier for the finite-dimensional
Hiai Problem 5.18, arXiv:2510.04691v3. It does not prove that problem's two
outer-power trace curvature suppliers, the inverse geometric-mean identity,
or the support-constrained semidefinite boundary extension.

For positive definite M and W and every real a >= 1, the reverse trace Young
bound is a Re Tr(M to exponent 1/a) <= Re Tr(M W to exponent 1-a)
+ (a-1) Re Tr W. The minimum over positive definite W is attained at
W = M to exponent 1/a. For a > 1, factor M to exponent one half as
U V with U = M to exponent one half W to exponent (1-a)/2 and
V = W to exponent (a-1)/2. Schatten Holder at (2/a, 2, 2/(a-1)) and
weighted scalar AM-GM give the bound. Gram traces prove nonnegativity
even though the mixed product need not be selfadjoint. At a=1 the
objective is independent of W. Empty matrix dimension remains in scope.
This is a classical supplier, not a new mathematical inequality. It does
not assert an attained positive definite optimizer for singular M.

## Verified locator

https://arxiv.org/abs/1811.01205v2
