---
bibkey: dlmf2026divisorpartition
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: Divisor power sums and finite geometric factors
doi: null
url: https://dlmf.nist.gov/27.2
claim: The divisor power sum at a negative complex parameter factors into finite geometric sums over prime powers; their root moduli give nonvanishing off the imaginary axis.
strata_touched:
  - D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros
license: citation-only
triage: anchor
---

# A shared chain for finite divisor factors

## Verified locator

The exact upstream locator is:
https://dlmf.nist.gov/27.2

Equation (27.2.10), also retrieved as https://dlmf.nist.gov/27.2.E10.tex,
states `sigma_alpha(N) = sum_{d|N} d^alpha`. Its following text explicitly
permits real or complex alpha. The pinned Mathlib source
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Field/GeomSum.lean
was checked locally: `geom_sum_eq` states
`sum_{j<n} q^j = (q^n-1)/(q-1)` under `q != 1`.

## Shared source chain and declaration bridges

For N>0, unique prime factorization writes every divisor uniquely as
`d = product_{p|N} p^j_p`, with `0 <= j_p <= v_p(N)`. For positive bases,
`d^(-s) = exp(-s log d)` and the real logarithm turns this finite product
into a sum. Expanding over the exponent choices gives
`sigma_{-s}(N) = product_{p|N} sum_{j=0}^{v_p(N)} (p^(-s))^j`.
This is the mathematical correspondence, not a claim that this module
adds a Lean theorem equating its product to a separately defined sigma.

- `localFactor`: a local representation of the standard finite geometric
  sum (标准构造的本地表示), with `q=(p:Complex)^(-s)` and length a+1.
  The definition accepts every natural p and a, including p=0, p=1 and a=0,
  using Lean's total complex-power convention. The zero theorems below
  retain the hypothesis that p is prime; no arbitrary-base extension is
  inferred from this larger definition domain.
- `partition`: a local representation of the standard divisor power-sum
  construction (标准构造的本地表示), via the product expansion above.
  The domain is positive N; N=1 gives the empty product 1.
- `local_factor_zero_re`: take moduli in the geometric-sum chain.
  If q=1, the sum is a+1, which is nonzero. Otherwise `geom_sum_eq`
  makes a zero imply `q^(a+1)=1`, hence `|q|=1`. For prime p>1,
  `|p^(-s)|=p^(-Re s)`; injectivity in the real exponent forces `Re s=0`.
  The local proof uses `Complex.norm_natCast_cpow_of_pos` and
  `Real.rpow_right_inj` at the same Mathlib pin.
- `partition_ne_zero_of_re_ne_zero`: each prime factor is nonzero by the
  preceding implication; a finite product of nonzero complex numbers is
  nonzero. No infinite-product convergence claim is involved.
- `partition_zero_re`: take the contrapositive of that finite-product
  nonvanishing result.

## What this note does and does not attest

Attested by this repository's own retrieval: the DLMF equation and explicit
complex-parameter sentence; the pinned Mathlib formula and the local
definitions and proof steps. The divisor-expansion and modulus bridges
are written above rather than attributed to a named DLMF zero theorem.

The round-19 source classification is received from issue #6298. Attribution
of these exact Lean signatures or an earliest-appearance claim to DLMF
would be `ASSUMED-UNVERIFIED` and is not made. The existing note and Citation
for `local_factor_eq_zero_iff` are outside this correction.
