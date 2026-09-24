---
slug: oeis-a331474-hankel-generating-function
bibkey: barry2020a331474
doi: null
url: https://oeis.org/A331474
triage: theorem
motivation_gids:
  - D5/S3/Constants/Moments/HankelJacobiDeterminant
---

# Barry's A331474 Hankel generating-function conjecture

## Problem

OEIS A331473 defines, at offset zero,

`s_n = Sum_{k=0..n} (-1)^(n-k) * binomial(2*k+2,k)`.

OEIS A331474 is its literal Hankel transform

`H_n = det(s_(i+j))_(0<=i,j<=n)`

and Paul Barry's January 17, 2020 FORMULA line conjectures the full identity

`Sum_{n>=0} H_n*x^n = (1 + 3*x + 16*x^2 - 8*x^3 + 36*x^4 - 12*x^5 + x^6 - x^7) / (1 + 7*x^2 + x^4)^2`.

The resolved statement is
`D5/S3/Constants/Moments/A331474HankelGeneratingFunction.a331474_hankel_generating_function`.
It is an equality for `PowerSeries.mk H`, so the left side is the actual
determinant sequence, not a recurrence-defined surrogate. The denominator has
constant coefficient 1 and the formal right side uses its unit inverse.

## Motivation

The displayed coefficients begin
`1, 3, 2, -50, -43, 535, 487, -4983, -4654, 43174` and have alternating-sign
blocks incompatible with a positive-real Gram argument. A proof therefore has
to retain the literal moment source and control its signed Hankel determinants
at every order.

## Gap

The exact source scope was pre-registered in issue #9676. A refresh on
2026-09-24 found A331474 still at revision 9, still marking Barry's formula
`(conjecture)`, and adding no proof reference. A331473 is revision 16 and still
contains the literal alternating-binomial formula above.

The bounded source-family search included Bojičić-Petković-Barry (2025),
Hacettepe Journal of Mathematics and Statistics 54, 1470-1478,
DOI 10.15672/hujms.1564485. The caller read the full nine-page primary PDF.
Its Theorems 3.1 and 5.1, after matching the first two source moments, predict a
third moment of 9 or 10 rather than the literal value 12, so they do not
subsume this source. An exact Crossref search for the A331474 identifier
returned zero records. arXiv and OpenAlex searches were rate-limited with HTTP
429, leaving that coverage gap. The joeis direct Hankel generator and loda
recurrence generator reproduce data but do not prove the bridge. These bounded
readings do not establish worldwide absence, exhaustiveness, or priority.

## Route

The proof uses the pinned Mathlib Catalan power-series equation, polynomial
basis-change determinants, matrix adjugates, Cramer identities, and formal
power-series inversion. The source-specific bridge is
`D5/S3/Constants/Moments/A331474HankelBridge.literal_hankel_eq_signed_kernel`.

1. Differentiate the Catalan series to obtain the literal unsigned moments,
   then derive two period-two tails and their continuant error identity.
2. Prove signed monomial and polynomial orthogonality for the monic continuants.
   The Gram diagonal entries are `(-1)^k`; negative norms are intentional.
3. Use monic Gram diagonalization and a division-free adjugate identity. The
   actual adjacent-column conversion has coefficient `c=-1`, and Cramer's
   identity gives the signed finite kernel for every `H_n`.
4. Derive the exact scalar recurrences for `p` and `u`, split by parity, and
   obtain the all-order recurrence for `H`. The values through `H_9`, including
   the `n=8` and `n=9` closure cases, follow from this bridge rather than a
   large finite determinant verification.
5. Check every coefficient after multiplication by `(1+7*x^2+x^4)^2`, then
   multiply by its unit inverse to obtain the full generating-function identity.

## Falsifier

Any natural index at which the determinant of the literal A331473 Hankel
matrix differs from the corresponding coefficient of Barry's rational series
would refute the claimed identity. A finite prefix agreement cannot prove the
statement; the formal theorem quantifies over every coefficient through an
identity of power series.

## Evidence

- Accepted Lean owners:
  `D5/S3/Constants/Moments/A331474HankelBridge.lean` and
  `D5/S3/Constants/Moments/A331474HankelGeneratingFunction.lean`.
- Sealed source SHA-256 values:
  `fb943e95c5b90a5e5b0477a755a06633b7937c98adb87fdb2d0b62ee179a85ee` and
  `62224f8050d6316388b15bbb7a665006ec628649b44dee0d759605ff9023c01d`.
- Three independent source reviews approved the mathematical proof with no
  remaining mathematical gap. Those reviews are supplied evidence, not a
  substitute for the repository's Lean report and admission checks.
- The bridge theorem states the determinant kernel, both scalar initial-value
  sets, and both quantified recurrences in one public declaration. The final
  theorem states the complete identity for `PowerSeries.mk H`.

## Triage

`theorem`; resolution `proved`. Both public theorems have `proof_shape:
content`: after all same-batch helpers are unfolded, the live chain contains
the Catalan-tail continuant error, signed orthogonality, monic Gram
diagonalization, division-free adjugate/Cramer conversion, scalar parity, and
the coefficientwise all-order recurrence. The admission basis is
`escape-witness`, and `utility: none` is accurate: these are general unbounded
mathematical theorems, not finite-prefix certificates, bounded enumerations,
checkers, or numeric reductions. The intermediate bridge receives no separate
open-problem resolution claim; only the final generating-function theorem is
the typed `OpenProblemResolutionClaim(Proved)` target.

## ASSUMED-UNVERIFIED

The arXiv and OpenAlex searches remain incomplete because their recorded
requests returned HTTP 429. Crossref, joeis, loda, and the cited paper delimit
the checked surfaces only. No global absence or worldwide priority claim is
made. The formal result settles the literal source statement; it does not
claim that every classical ingredient in its proof is new.
