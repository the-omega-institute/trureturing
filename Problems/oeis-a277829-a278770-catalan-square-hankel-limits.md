---
slug: oeis-a277829-a278770-catalan-square-hankel-limits
bibkey: kotesovec2016a277829a278770
doi: null
url: https://oeis.org/A277829
triage: theorem
motivation_gids:
  - D5/S3/Constants/Moments/CatalanSquareHankelLimits.catalan_square_hankel_log_limits
---

# A277829 and A278770: squared-Catalan Hankel limits

## Problem

Let

```text
C_m = binomial(2*m,m)/(m+1),
D_r(n) = det[(C_(i+j+r))^2] over i,j in Fin n.
```

The empty determinant is one. Prove both conjuncts

```text
lim_(n->infinity) log(D_1(n))/n^2 = 2*log(2),
lim_(n->infinity) log(D_2(n))/n^2 = 2*log(2).
```

These are exactly Kotesovec's November 29, 2016 A277829 conjecture and
November 28, 2016 A278770 conjecture. Their one-based programs use
`C_(i+j-1)^2` and `C_(i+j)^2`, respectively, so the zero-based shifts are
exactly one and two. The source assertions were preregistered in
https://github.com/the-omega-institute/trureturing/issues/9530 before the
proof probes.

## Motivation

The two OEIS sequences differ only by the adjacent Hankel shift, while their
published conjectures assert the same exact logarithmic rate. A joint formal
endpoint keeps both literal source assertions visible and lets the common
moment, Gram, and asymptotic argument discharge them without identifying the
two determinant sequences.

## Route

The supporting module defines the scaled beta Catalan moment law and proves
the literal identity `integral (4*x)^m = C_m`. Fubini gives the square
`C_m^2` as the moment of the product of two independent scaled beta
variables. Weighted powers of that product coordinate are linearly
independent in `L2`; their Gram matrices are the two shifted Hankel matrices.
This proves strict positivity of every determinant for both shifts, including
the size-zero determinant.

For the upper estimate, monic affine Chebyshev-T polynomials on `[0,16]`
replace the power basis without changing the Gram determinant. Their uniform
supremum bound and the positive-definite Hadamard inequality give

```text
D_1(n) <= 4^n  * 16^(n*(n-1)/2),
D_2(n) <= 16^n * 16^(n*(n-1)/2).
```

For every `0<delta<8`, the beta density has a positive uniform lower bound
on a compact central rectangle. After transporting Chebyshev-U
orthogonality to that rectangle, the proof bounds the full normalized Gram
quadratic form below, not only its diagonal. A positive-semidefinite
remainder and all principal minors yield one constant `C>0`, independent of
`n`, such that for `r=1,2`

```text
(C*delta^r)^n * ((8-delta)*pi/2)^n
  * ((8-delta)/2)^(n*(n-1)) <= D_r(n).
```

Taking logarithms, dividing by `n^2`, and moving `delta` to zero squeezes
both rates to `log 4 = 2 log 2`.

## Gap

The adjacent Lin note records the Catalan density and product-density route.
The Simon note records the Erdos-Turan regularity criterion, monic norm
asymptotics, and interval capacity. Together they give a separate ordinary
classical corollary with the same two limits. The Lean proof is elementary
and does not formalize that literature derivation.

The bounded prior audit described in the Kotesovec note found no explicit
settlement of either exact named conjecture in its inspected scope. It is not
a worldwide absence or priority certificate, and this dossier does not claim
full publication or global novelty.

## Falsifier

A failure of either all-n positivity statement, or a subsequence on which
either displayed normalized logarithm stays away from `2*log(2)`, would
refute the formal target. Finite numerical agreement alone cannot prove either
limit.

## Evidence

`D5.S3.Constants.Moments.CatalanSquareHankelGrowth.catalan_square_hankel_det_positive`
proves both all-n positivity conjuncts, and
`D5.S3.Constants.Moments.CatalanSquareHankelGrowth.catalan_square_hankel_det_upper`
proves both explicit upper bounds. The exact named settlement is
`D5.S3.Constants.Moments.CatalanSquareHankelLimits.catalan_square_hankel_log_limits`.
Formal source hashes, statement identities, declaration types, and axiom
closures are supplied by the canonical Lean report rather than duplicated in
this narrative.

## Triage

First tier; `admission_basis: open-problem-resolution`; preregistration issue
9530. The two Growth theorems have `proof_shape: content` and
`admission_basis: escape-witness`. The Limits endpoint has
`proof_shape: content` and
`admission_basis: open-problem-resolution`. None of these declarations is a
bounded enumeration, checker, numeric reduction, or certified finite
instance, so `utility: none` is accurate.

## ASSUMED-UNVERIFIED

The primary-source readings and bounded prior searches are inherited from the
supplied caller and independent source-audit results. This metadata pass did
not independently repeat them. The search limits, including one HTTP 403 and
one HTTP 429, do not rule out unindexed literature, textbooks, private work,
or later solutions. Kernel verification settles the displayed formal
conjunction but does not establish worldwide priority or publication status.
