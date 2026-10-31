---
slug: oeis-a391810-laurent-first-moment
bibkey: hanna2025a391810
doi: null
url: https://oeis.org/A391810/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/HannaLaurentRowSums.series_coefficient
  - D5/S3/ArithSums/HannaLaurentRowSums.row_degree
---

# The first weighted moment of A391810

## Problem

Paul D. Hanna's OEIS A391810, revision 39, formula (3), states:

> (3) Sum_{k=0..floor((n+1)/2)^2} k * T(n,k) = 1 for n >= 1 (conjecture).

The original definition is:

> Irregular triangle, read by rows, where row n lists the coefficients of nonpositive powers of x in the doubly infinite series Sum_{k=-oo..oo} x^k * (1 - x^k)^(n+k) for n >= 1.

Thus, for every positive natural n, expand
`S_n(x)=Sum_{j in Z} x^j*(1-x^j)^(n+j)` formally at zero and let
`T(n,k)=[x^(-k)]S_n(x)`. The outer sum includes every integer j;
negative integer powers use Laurent-field inverses. The row includes its
constant coefficient at k=0 and its exact inclusive final index
`floor((n+1)/2)^2`. Coefficients and the weighted row sum are signed integers.
The literal Laurent realization uses rational coefficients and the exact
integer-to-rational coefficient bridge. The shared library note's claim
quotation concerns formula (2); the quoted formula (3) is the distinct target here.

## Motivation

This is a Tier 1 explicitly published universal coefficient identity.
The existing coefficient bridge and degree bound turn its infinite-series
definition into an exact finite polynomial question without changing the
row or endpoint. The exact event and bounded qualification are registered at
https://github.com/the-omega-institute/trureturing/issues/24461.
The already established formula (2) is reused and is not another resolution.

## Gap

The caller-supplied source and reuse qualification reports no settlement of
this exact formula within its successful bounded searches. This is a bounded
qualification, not a claim of global absence or priority. The current official
OEIS export at
https://raw.githubusercontent.com/oeis/oeisdata/master/seq/A391/A391810.seq
contains the quoted definition and formula (3), with revision identifier 39.
Its SHA256 is
`49bbf5e8e42f91b6a3d838b2ce5c311eca58af74a83a4f6f684b09e1ddf0da83`.
The missing mathematical step beyond the reused coefficient and support
results is the first weighted moment; the result below supplies that step
for every positive natural n. No corresponding theory volume was identified
by the qualified exact-source searches.

## Route

Use the existing polynomial
`P_n(y)=-1+Sum_{j=1..n} y^j*(1-y^j)^(n-j)`.
The frozen theorem
`D5/S3/ArithSums/HannaLaurentRowSums.series_coefficient`
identifies its coefficient at k with the literal Laurent coefficient at -k,
including k=0. The frozen degree bound makes the published finite interval
contain every polynomial coefficient.

Differentiate only this finite polynomial. At n=1 the derivative at y=1 is
one. For n>=2, every differentiated summand with j<=n-2 vanishes at one.
The last two differentiated terms contribute `-(n-1)` and `n`, respectively,
so `P_n'(1)=1`. The polynomial derivative coefficient identity gives
`Sum_{k=0..floor((n+1)/2)^2} k*T(n,k)=1` in the integers.
Transfer that same equality to the rational literal Laurent coefficients.
The bilateral series itself is never evaluated at x=1.

## Falsifier

A positive natural n whose exact signed weighted sum over the full published
inclusive interval differs from one would refute formula (3). A computation
that drops the constant coefficient, truncates the bilateral family before
establishing the coefficient bridge, changes the endpoint, or takes absolute
values would address a different question and is not such a falsifier.

## Evidence

`D5/S3/ArithSums/HannaLaurentFirstMoment.result` states both the integer
weighted equality and its literal rational Laurent counterpart, with the full
positive-natural telescope and exact inclusive endpoint. Its two private
helpers establish the derivative evaluation and the integer moment and are
consumed in that proof. The retained Reg mirror reconstructs this same full
statement and retains both conjuncts.

Every authored mathematical declaration has `proof_shape: bind-only`.
The public result uses `admission_basis: open-problem-resolution` for the
single preregistered external formula (3); the helpers have their actual
proof consumers. There is no separate escape-witness claim, finite-instance
delivery, new axiom, or second claim for formula (2).

## Triage

The exact source event is a universal theorem question, with its definition,
signs, coefficient domain and endpoint retained.

### What the settlement shows

- **Proved** (`D5/S3/ArithSums/HannaLaurentFirstMoment.result`): the decisive
  mechanism is `P_n'(1)=1`, obtained from the two surviving differentiated
  boundary terms, together with the existing coefficient bridge. The result
  covers every n>=1 without parity restrictions or a finite ceiling, in both
  integer row entries and literal rational Laurent coefficients. It needs
  no analytic convergence assumption or evaluation of the bilateral sum.
- **Proved** (`D5/S3/ArithSums/HannaLaurentRowSums.row_degree`): the published
  endpoint contains the full support. This is an upper bound; equality with
  the degree or optimality for each n is not asserted by the first-moment proof.
- **Open**: extensions to nonpositive row indices, other expansion conventions
  or coefficient fields, and sharpness of the endpoint are not established
  by this delivery. The original positive-n domain is retained throughout.
- **Proved** (`D5/S3/ArithSums/HannaLaurentFirstMoment.result`): formula (3)
  supplies exactly its weighted-sum premise to any argument that uses it.
  The previously proved formula (2) retains its independent proof and scope.
  No other source argument or conjecture is certified merely by this premise.
- **Open candidate, formula (4)**: the source also asks whether
  `Sum_{k=0..floor((n+1)/2)^2} k^2*T(n,k)=-(2*n-5)` for every n>=2.
  A second-derivative investigation would be a separate target; no such
  identity or extension is proved here.
- **Open candidate, formula (5)**: the source also asks whether
  `Sum_{k=0..floor((n+1)/2)^2} -(-1)^k*T(n,k)=2*round(2^n/3)=2*A001045(n)`
  for every n>=1, with A001045 the Jacobsthal numbers. Evaluation at minus
  one is a possible separate route, not a consequence certified here.

## ASSUMED-UNVERIFIED

Global prior solvedness and priority outside the supplied successful bounded
screens remain ASSUMED-UNVERIFIED. The conjecture label alone supplies no
global absence evidence. Independent final delivery reviews, required CI,
publication and merge to dev remain separate obligations. The neighboring
formulas (4) and (5) are candidates only; they and other A391810 or A391811
questions are not settled by this result. The audit's continuation is unknown
and entails no undecidability or inexhaustibility claim.
