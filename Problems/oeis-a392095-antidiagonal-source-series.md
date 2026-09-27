---
slug: oeis-a392095-antidiagonal-source-series
bibkey: kurkov2025a392095
doi: null
url: https://oeis.org/A392095
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries
---

# The A392095 column and A088713 source series

## Problem

Mikhail Kurkov's A392095 (December 30, 2025) states:

> Array read by downward antidiagonals: A(n,k) = A(n-1,k+1) + Sum_{j=0..k} A(n-1,j)*A(k-j,0) with A(0,k) = 1.

> Conjecture: A(n,0) = A088713(n+1).

Paul D. Hanna's A088713 (October 12, 2003) states:

> G.f. A(x) satisfies A(x/A(x)) = 1/(1-x).

Both sequences start at index zero. A088713 has constant coefficient one.
The exact sources, author lines, immutable locators and licenses are in
`Library/Recurrence/kurkov2025a392095.md` and
`Library/Recurrence/hanna2003a088713.md`.

The full assertion concerns a total array T : N -> N -> N with
T(0,k)=1 for every k and
T(n+1,k)=T(n,k+1)+sum(j=0..k) T(n,j)*T(k-j,0) for every n,k.
There is a unique such T. Independently there is a unique F in Q[[X]]
with F(0)=1 and F(X*F^(-1))=(1-X)^(-1). There is a unique b : N -> N
whose rational coefficient series satisfies that equation; b(0)=1,
[X^m]F=b(m) for every m, and T(n,0)=b(n+1) for every n, including zero.
Inverses here are multiplicative unit inverses, and the inner substitution
series has zero constant coefficient. No extra source equation is assumed.

## Motivation

This is a first-tier named OEIS conjecture from 2025, connecting an
antidiagonal recurrence to a separately specified 2003 generating series.
The original target is preregistered in
https://github.com/the-omega-institute/trureturing/issues/8186.
The theorem retains independent source existence and uniqueness and the
natural coefficient witness, so identification cannot hold vacuously.

## Gap

The quotient-composition comparison alone does not identify the recurrence's
column. The necessary bridge sums the recurrence over every row and proves
that H=1+X*C, where C is the column series, satisfies Hanna's equation.
The factor X explains the one-step coefficient shift.

## Route

The array is constructed by the lexicographic measure (n+k,n); induction
first on n+k and then on n proves uniqueness. Rational source coefficients
are constructed recursively from the equation without reference to the
array. Constant-one quotient triangularity determines the next coefficient
and proves source uniqueness, including degree zero.

Write R_r for row r, C for the first column, H=1+X*C, I=H^(-1), and Y=X*I.
The recurrence gives H*R_r=T(r,0)+X*R_(r+1), hence
R_r=I*T(r,0)+Y*R_(r+1). Finite telescoping through N rows gives
R_0=I*sum(i<N) T(i,0)*Y^i+Y^N*R_N.
At degree d, take N=d+1; the remainder is divisible by X^(d+1).
Consequently C(Y)=H*R_0. Since R_0=(1-X)^(-1), substitution yields
H(Y)=1+Y*C(Y)=1+X*R_0=R_0. Source uniqueness identifies H with F.
Its positive coefficients are natural column entries and its constant
coefficient is one, yielding b and its uniqueness by coefficient extraction.

## Falsifier

A failure at any natural n of T(n,0)=b(n+1), or two distinct normalized
rational solutions of the specified equation, contradicts the result.
Neither finite data agreement nor uniqueness conditional on unproved
existence suffices. The theorem supplies all existence witnesses.

## Evidence

The Lean module is
`D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.lean`, with the six
definitions `array`, `IsArray`, `IsSource`, `phi`, `sourceCoeff`,
`sourceSeries` and the single theorem `result`. The source statements and
original proof construction are retained from PR8211.

The ordered library search on September 21, 2026 (Singapore) examined D5
for `A392095`, `A088713`, `quotient_triangular` and quotient-substitution
patterns. The frozen theorem
`D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.quotient_triangular`
supplies the two normalized coefficient comparisons directly over Q; it
requires both constant coefficients to be one. Its theta-series conclusion
does not identify this array. The all-row telescoping bridge remains needed.

Pinned Mathlib at `db584cd6d46c92f209a44c0f1c829460d327499d` has no hits for
the two OEIS IDs or `quotient_triangular`. The actual contracts read in
`PowerSeries/Substitution.lean`, `Inverse.lean` and `WellKnown.lean` supply
`coeff_subst'`, `mul_invOfUnit`, `invOfUnit_mul` and
`mk_one_mul_one_sub_eq_one`, which the proof uses. These are general
power-series operations, not the complete recurrence-to-column theorem.
Subsequent GitHub code searches for `"A392095" language:Lean`,
`"A088713" language:Lean` and `"quotient_triangular" language:Lean`
returned no indexed matches. The related external source
`kim-em/hex-dev` at `615181aea596561e0530bfeece2106ee25cc8095` was also
inspected: `HexTruncatedSeries/Revert.lean` provides two-sided truncated
compositional inversion for zero constant coefficient and invertible
linear coefficient; `Comp.lean` supplies finite composition and associativity;
`HexTruncatedSeriesMathlib/Newton.lean` connects truncation to Mathlib's
unit inverse and substitution. These contracts do not assert the array
recurrence or column identity. Its Lean v4.34.0 and Mathlib
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` differ from the project's
v4.33.0 and pinned Mathlib, excluding dependency form under spec A17.2.
Its Apache-2.0 source was considered for transplantation, but no missing
exact target result was identified; the required power-series operations
are already present in the pinned Mathlib. No code was transplanted.

## Triage

`theorem`: an unbounded symbolic identity, with no finite-only replacement.
The local coefficient telescoping argument is the substantive bridge;
the imported triangularity is used inside that proof. `utility: none`
applies because the result is neither a bounded enumeration nor a
checker, numerical reduction, or isolated certified finite instance.

## ASSUMED-UNVERIFIED

The source-to-formal identification and proof classification require
independent semantic review. Library and code-index searches are bounded:
differently phrased or unindexed equivalents remain possible. The fixed
official export was read in full; current live OEIS freshness and worldwide
priority were not independently checked here. The earlier source audit's
broader prior-resolution search is not fresh evidence from this repair.
No authorship, originality, or programme-credit conclusion follows from
these searches. Kernel, admission and resolution status belong to canonical
machine outputs, not this dossier.
