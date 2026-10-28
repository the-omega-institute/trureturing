---
slug: oeis-a391810-full-laurent-row-sums
bibkey: hanna2025a391810
doi: null
url: https://oeis.org/A391810/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/HannaLaurentRowSums
---

# The full Laurent rows in A391810 sum to zero

## Problem

Paul D. Hanna's OEIS A391810 formula (2) states:

> (2) Sum_{k=0..floor((n+1)/2)^2} T(n,k) = 0 for n >= 1 (conjecture).

The defining NAME is:

> Irregular triangle, read by rows, where row n lists the coefficients of nonpositive powers of x in the doubly infinite series Sum_{k=-oo..oo} x^k * (1 - x^k)^(n+k) for n >= 1.

Formula (1) identifies the truncated Laurent expansion, including the constant
term, with `Sum_{k=0..floor((n+1)/2)^2} T(n,k)*x^(-k)`.
All rows with positive integer n are included. Expansion takes place at zero;
negative integer exponents mean Laurent-field inverses.

## Motivation

This is a Tier 1 explicitly published arithmetic conjecture. Its universal
endpoint is the full row sum, with the exact inclusive row support bound.
The prospective question and its source qualification are registered at
https://github.com/the-omega-institute/trureturing/issues/16322.

## Gap

The source qualification supplied bounded searches of the current official
A391810 and A391811 records, exact-ID OEIS and Crossref results, SeqFan,
the full primary TeX of arXiv:2607.24832v1 and JIS Article 26.1.8,
and four public Lean collections. Those searches found no settlement of the
exact question. Repository searches included private D5 declarations and the
pinned Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
The current lane search again found no exact identifier or corresponding
bilateral-row result. Existing Laurent and finite-binomial infrastructure is
reused directly. These bounded checks do not establish global priority.

Some search providers returned HTTP 403, rate limits, interstitial pages or
bot challenges; those responses provide no negative evidence. OEIS history
was inaccessible, so the version evidence is the matching official current
JSON and internal page, not a complete revision-history audit.

## Route

Let y=x^(-1). The negative outer indices -1 through -n contribute
`y^j*(1-y^j)^(n-j)` for j=1 through n. The outer index -(n+1)
contributes constant -1. Every other outer index has strictly positive
Laurent order and contributes nothing to a nonpositive coefficient. A uniform
lower support bound and finite coefficient contribution sets certify the
bilateral formal sum, rather than assuming an infinite sum exists.

The inverse-variable polynomial is therefore
`P_n(y)=-1+Sum_{j=1..n} y^j*(1-y^j)^(n-j)`.
The exact coefficient bridge proves its integer coefficient at m is the
coefficient at -m of the original rational Laurent series.

For even n, reflecting j to n+1-j cancels the highest monomials of the
binomial expansions. Every remaining exponent j*(r+1) has
`j+(r+1)<=n` and is bounded by `floor((n+1)/2)^2`.
For odd n, the highest monomials themselves satisfy the same bound.
Thus no nonpositive coefficient is omitted by the published row endpoint.

Evaluate this finite polynomial at one. Only j=n survives, with value one,
which cancels its constant minus one. Polynomial evaluation as a sum of
coefficients proves the integer row sum. The coefficient bridge transfers
that sum and the full support bound to the original bilateral Laurent series.
No evaluation of the original infinite expression at one is used.

## Falsifier

A positive n with a nonzero full inclusive row sum would falsify formula (2).
A nonpositive Laurent coefficient disagreeing with the integer polynomial,
or a nonzero coefficient beyond the published bound, would falsify the
corresponding bridge or support assertion.

## Evidence

The mathematical declarations are in
`D5/S3/ArithSums/HannaLaurentRowSums.lean`, with exposition in its canonical
Blueprint Scribe. `result` states the integer zero row sum, the corresponding
rational Laurent zero row sum, and vanishing of every coefficient beyond the
inclusive bound. `series_coefficient` identifies every nonpositive
coefficient with its integer polynomial coefficient.

The expanded proof uses pinned Laurent order and formal-sum interfaces,
finite binomial expansion, a reflected cancellation, polynomial degree
bounds, and polynomial evaluation. Its declaration classification is
conservatively bind-only; the prospective basis is
`open-problem-resolution`. Consumed helpers organize these same arguments
and do not establish a separate novelty claim.

## Triage

The source is an explicit published conjecture; its integer coefficient
identification and exact row endpoint are part of the mathematical claim.
Independent source fidelity, admission and frozen delivery are separate
from this draft's mathematical proof.

### What the settlement shows

- **Proved** (`D5/S3/ArithSums/HannaLaurentRowSums.series_coefficient`,
  `D5/S3/ArithSums/HannaLaurentRowSums.result`): the decisive mechanism is the
  finite polynomial `P_n(y)=-1+Sum_{j=1..n} y^j*(1-y^j)^(n-j)`.
  The coefficient bridge includes the constant coefficient. For positive n,
  evaluation at y=1 leaves only the j=n term, whose value one cancels minus
  one. The zero sum is thus symbolic for every positive integer n, with no
  parity restriction or finite-n ceiling. It does not require numerical
  convergence or substitution into the bilateral expression at x=1.
- **Proved** (`D5/S3/ArithSums/HannaLaurentRowSums.row_degree`,
  `D5/S3/ArithSums/HannaLaurentRowSums.result`): the degree inequality ensures
  that the published inclusive endpoint omits no nonpositive coefficient.
  The polynomial degree inequality itself holds for every natural n;
  the original Laurent coefficient bridge and zero-row-sum conclusion retain
  `0<n`. No additional parity hypothesis needs to be imposed or removed.
- **Computed** (`python3 -c 'n=0; print(((n+1)//2)**2, -1 + sum(1**j * (1-1**j)**(n-j) for j in range(1,n+1)))'`,
  output `0 -1`): the finite polynomial expression at n=0 has bound zero and
  row sum minus one. Positivity cannot be deleted from that expression's
  zero-sum assertion. This is not an interpretation of a source-defined
  row S(0), which the published positive-n question does not provide.
- **Open**: `row_degree` proves an upper bound, not equality of the degree
  with the bound or optimality of that endpoint. Sharpness for each n,
  a smaller uniform endpoint, and extensions to other coefficient fields,
  expansion conventions or nonpositive row indices have not been proved here.
- **Proved** (`D5/S3/ArithSums/HannaLaurentRowSums.series_coefficient`,
  `D5/S3/ArithSums/HannaLaurentRowSums.row_degree`,
  `D5/S3/ArithSums/HannaLaurentRowSums.result`): these statements justify
  formula (1)'s finite nonpositive truncation and formula (2)'s zero row sum
  in their original positive-n domain. Formula (2) can therefore supply that
  exact premise wherever a source argument assumes it.
- **Open**: no other source conclusion depending on formula (2) has been
  reverified here; its remaining hypotheses and proof steps would still need
  checking. No other A391810 conjecture is settled, and no new claim about
  the related A391811 squared-sum sequence is established. Applicability of
  this cancellation argument to those neighboring questions remains open.

## ASSUMED-UNVERIFIED

Literature completeness outside the bounded checked surfaces and global
priority are unverified. No other A391810 or A391811 conjecture is settled
by this result. The mirrored information audit is unfinished. The full-telescope
result realization has an unfinished observation-dependence obligation
`-1 != -(Polynomial.coeff 1 1)+1`. No compiled Reg mirror is retained.
The unfinished audits of `summand_order`, `summand_lower_bound`,
`coefficient_finite`, `series_coefficient`, `row_degree`, and `result`, including
this proof gap and missing exact source-selection binding, are disclosed in
https://github.com/the-omega-institute/trureturing/issues/16322 under the
repository's registration exception. Registration completion is unverified;
no `declared_validated` status, admitted freeze or merged delivery is asserted.
