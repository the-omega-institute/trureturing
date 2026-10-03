---
bibkey: cbirkbeck2026chebotarev
authors: Chris Birkbeck and the Chebotarev density contributors
year: 2026
title: Chebotarev density in Lean
doi: null
url: https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88
claim: For a finite Galois extension of number fields, the prime ideals with a specified Frobenius conjugacy class have Dirichlet density equal to that class's cardinality divided by the Galois group's cardinality.
strata_touched:
  - D5/S3/Factorization/Galois/Chebotarev/Main
  - D5/S3/Factorization/Galois/Chebotarev/Abelian
  - D5/S3/Factorization/Galois/Chebotarev/FixedFieldDensity
license: Apache-2.0
triage: anchor
---

# Chebotarev density in Lean

## Verified locator

The immutable upstream source is
<https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.
Its `CebotarevDensity` sources supply the prime-ideal Dirichlet-density
argument, Frobenius counting over fixed fields, the cyclotomic crossing,
and the abelian-to-general Galois reduction. The source collection is
AINTLIB revision `e0284fdbcab2d6a1c3246b7ea362f4b96d7b2e10`.

For a finite Galois extension $L/K$ and a conjugacy class $C$ in
$\operatorname{Gal}(L/K)$, the set of nonzero prime ideals of $K$
unramified in $L$ whose Frobenius class is $C$ has density
$|C|/[L:K]$. The density uses the prime-ideal norm Dirichlet series
as its denominator. The rational-prime formulation takes $K=\mathbb Q$.
This theorem supplies no effective error bound or bound for the least
prime in that set.

The content port keeps the prime, nonzero-ideal and unramified
conditions of the selected source interface. Its cyclotomic crossing
also retains the explicit modulus and discriminant coprimality
conditions. The supporting analytic statements concern summability,
Euler products and their logarithmic tails; the arithmetic statements
concern ideal-congruence lattice counts and residue fibers.

The source collection pins Lean `v4.31.0-rc2` and Mathlib
`d90090f647ca`; the content port targets the repository's Lean
`v4.33.0` and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Source declarations already supplied by the target Mathlib are used
directly inside the remaining proofs. Matching upstream names alone
do not establish matching hypotheses or conclusions.

The source is released under Apache License 2.0. The repository's
root `LICENSE` supplies that license text. The original copyright,
license and author notice in the Frobenius source is retained in its
content owner; the selected source collection has no separate `NOTICE`
file. The mathematical conclusions of the port are those checked by
the Lean kernel under their displayed hypotheses and axiom closures.
