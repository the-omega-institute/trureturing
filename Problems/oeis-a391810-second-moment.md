---
slug: oeis-a391810-second-moment
bibkey: hanna2025a391810
doi: null
url: https://oeis.org/A391810/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/HannaLaurentRowSums
---

# The full signed Laurent second moment in A391810

## Problem

Paul D. Hanna's OEIS A391810 revision 39 formula (4) states:

> (4) Sum_{k=0..floor((n+1)/2)^2} k^2 * T(n,k) = -(2*n-5) for n >= 2 (conjecture).

The source defines T(n,k) as the coefficient at zero of x^k times the
bilateral series `Sum_{j=-oo..oo} x^j*(1-x^j)^(n+j)`, expanded formally
at zero. Equivalently it is the series coefficient at -k. All integer
outer indices, the constant coefficient, and both finite-sum endpoints are
included. Negative integer exponents are Laurent-field inverses. The bound
is natural division `(n+1)/2` followed by squaring. The right side uses
signed integer subtraction and negation, then a rational cast.

## Motivation

This is the explicitly posed formula (4), distinct from formula (2)'s zero
row sum and formula (3)'s first moment. The exact prospective source event,
forecasts and strict preregistration are associated with
https://github.com/the-omega-institute/trureturing/issues/24520 and
https://github.com/the-omega-institute/trureturing/issues/24520#issuecomment-6537206052.
Neither earlier moment is counted as this question's resolution.

## Gap

The official revision 39 export has SHA256
`49bbf5e8e42f91b6a3d838b2ce5c311eca58af74a83a4f6f684b09e1ddf0da83`.
Its formula (4) contains the exact quantifiers and signed expression above.
The bounded source qualification reused the earlier official OEIS,
Crossref, SeqFan, arXiv:2607.24832v1, JIS Article 26.1.8 and public Lean
collection searches. The subsequent source delta inspected 79 changed
research paths, including 60 D5 paths and 156 private declaration starts,
at dev `b1a09a0eb65b72a5e37289484e41c28aa0fa100d` relative to
`66c45b655013f43de728fcab36d99df1e61f9da3`; it found no exact supplier in
that scope. Eight available ownership states identified no formula (4)
owner. These bounded observations are not a proof of global absence.

## Route

The inherited `HannaLaurentRowSums.series` is the full formally summable
bilateral Laurent series. Its `series_coefficient` theorem identifies every
nonpositive coefficient with the integer coefficient of
`P_n(y)=-1+Sum_{q=1..n} y^q*(1-y^q)^(n-q)`, where y=x^(-1).
The inherited `row_degree`, `rowBound` and `rowEntry` supply the exact
inclusive support and integer polynomial interface. No new series or T
is defined. Only the finite polynomial is evaluated at one.

### Euler-operator calculation

For E=y*d/dy, the coefficient at k of E^2(P) is k^2 times that of P,
and E^2 does not increase polynomial degree. Evaluation at one is therefore
the full coefficient moment through the published endpoint.
For `y^q*(1-y^q)^m`, that evaluation is q^2, -3*q^2, 2*q^2, or zero
according as m is 0, 1, 2, or at least 3. For n>=3 the final three terms
give `n^2-3*(n-1)^2+2*(n-2)^2=-(2*n-5)`. For n=2 the two terms give
4-3=1. The constant -1 contributes zero. The exact coefficient bridge and
integer-to-rational cast yield the original Laurent statement.

## Evidence

`D5/S3/ArithSums/HannaLaurentSecondMoment.result` has parameters
`(n : ℕ) (hn : 2 ≤ n)` and conclusion

```lean
(∑ k ∈ Finset.range (((n + 1) / 2)^2 + 1),
  (k : ℚ)^2 * (HannaLaurentRowSums.series n (by omega)).coeff (-(k : ℤ))) =
  (-(2 * (n : ℤ) - 5) : ℤ)
```

The declaration is conservatively `proof_shape: bind-only`, with
`admission_basis: open-problem-resolution` for the exact external question.
Its consumed private helpers organize polynomial differentiation,
coefficient weighting and the boundary calculation; they make no separate
escape-witness or mathematical novelty claim. The matching Blueprint
contains the mathematical statement and derivation.

## Falsifier

Any natural n>=2 for which the literal full coefficient sum differs from
`-(2*n-5)` would refute formula (4). A finite ceiling on n, a missing
constant or inclusive endpoint, natural subtraction on the right, or a
substitution into the bilateral series at one would change this question.

## Triage

The result addresses formula (4) for every natural n>=2 in the formal
Laurent expansion at zero. It claims neither optimality of the support
bound nor another OEIS formula. Its canonical frozen declaration and typed
resolution link identify this exact source statement. There is no justified
successor claim here.

### What the settlement shows

- **Proved** (`D5/S3/ArithSums/HannaLaurentSecondMoment.result`): the
  Euler operator reduces the full second moment to the last three finite
  polynomial terms for n>=3, with n=2 included separately. The proof covers
  all natural n>=2 without a parity restriction or finite ceiling.
- **Proved** (`D5/S3/ArithSums/HannaLaurentRowSums.series_coefficient`,
  `D5/S3/ArithSums/HannaLaurentRowSums.row_degree`): the inherited bridge and
  support bound identify every coefficient needed by the original question.
  These prerequisites are reused rather than counted as a new resolution.
- **Open**: the support bound's sharpness, other moment identities and
  other source conclusions are outside this result. Formula (4) supplies
  its exact premise to arguments that require it; no such argument's other
  hypotheses or conclusions have been reverified here.

## ASSUMED-UNVERIFIED

Global solvedness and priority remain unverified. The bounded searches do
not close the SeqFan, revision-history, citation-chain or global-literature
gaps. The mirrored Reg source compiles its full-telescope equivalence, actual
positive law, whole-family variation and sensitivity, and nonconstant
coefficient observation. Its source binding remains `declared_unresolved`,
with no certificate. The current diagnostic is `IE-C050 ClosedTruthReadout`,
`reason=unclassified_form`, `rule=source.coordinate_dependency`,
`missing=1;selected=#[0, 2];scope=3`: the selected original coefficient
also depends on the positivity proof derived from binder hn. Missing evidence
is an accepted exact source-coordinate binding of this proof-dependent
coefficient observation. Assessment beyond that first boundary is unverified.
The unfinished registration is disclosed in
[audit issue 24562](https://github.com/the-omega-institute/trureturing/issues/24562).
No `declared_validated`, CI success, merge or dev publication is asserted here.
