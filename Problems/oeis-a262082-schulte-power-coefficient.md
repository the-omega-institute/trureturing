---
slug: oeis-a262082-schulte-power-coefficient
bibkey: schulte2015a262082
doi: null
url: https://oeis.org/A262082
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers
---

# Schulte's implicit-series power coefficients

## Problem

For every positive n, the native equation is
P_n=1+X*P_n^n+X²*P_n^(2n)+X³*P_n^(3n).
The source formula is:

> B(m,n,k) = m/(n*k+m) * Sum_{j=0..k} (-2)^j*binomial(n*k+m,j)* binomial(3*n*k+3*m-2*j,k-j) for m > 0, n > 0, and k >= 0. (conjectured)

The complete target requires a unique integer formal power series solution
and this rational image of every coefficient of every positive power.
It includes k=0, both sum endpoints and unbounded k. The separate
lattice-path and logarithmic conjectures are outside this target.

## Motivation

The question is the full Schulte coefficient formula for powers of the
native implicit family, rather than the ordinary quadrinomial polynomial
identity A008287. Unique existence is over integer formal power series;
the coefficient identity is stated after the canonical map into rationals.

## Gap

The [original entry](https://oeis.org/A262082/internal) and
[official source snapshot](https://raw.githubusercontent.com/oeis/oeisdata/49db7744e1fdbefbe376d1d018370c017d4c288b/seq/A262/A262082.seq)
state this formula as conjectured. Bounded literature and duplicate
readings are in [#30449](https://github.com/the-omega-institute/trureturing/issues/30449).
Their scope does not establish global historical openness or priority.
The contraction, Lagrange and A008287 results supply the series and
coefficient interfaces used in the complete native theorem.

## Route

Coefficient agreement below degree d is preserved by powers and products.
Multiplication by X increases agreement to degree d+1. The existing
normalized contraction theorem constructs the integer solution. Every
solution has constant coefficient one, giving unrestricted uniqueness.
Mapping integer coefficients into the rationals preserves the equation.

Put Q(t)=1+t+t²+t³ and U(y)=y*P_n(y^n). Then U=y*Q(U^n), and
[y^(nk+m)]U^m=[X^k]P_n^m. Apply the existing Lagrange theorem at
degree N=nk+m and power m, with factor Q(y^n). Expansion transports
its other coefficient from degree nk to degree k in Q(t)^N. The existing
A008287 expansion supplies the alternating sum. Its hypothesis k≤3N
follows from n≥1 and m≥1; N is nonzero. No positive lower bound on k
is used.

## Falsifier

A positive natural n with no unique integer solution of the native
equation, or a native integer solution with positive m and a natural k
whose rational coefficient differs from the displayed sum, would refute
the full event. A finite coefficient check cannot establish it.

## Evidence

The result is
`D5.S3.Combinatorics.PowerSeries.SchulteImplicitQuadrinomialPowers.result`.
This canonical S3 source is awaiting independent review and future canonical freezing.
Its two conjuncts retain unique integer-series existence and the formula
for every native integer solution, every positive m and every natural k.
The direct suppliers are
`PowerSeriesNormalizedContraction.exists_unique_fixed`,
`NonnestingOneThreeTwoTwo.lagrange_coefficient` and
`SchulteQuadrinomialAlternatingBinomialExpansion.result`, at their
existing D5 declaration addresses. Pinned Mathlib supplies `expand`,
`coeff_expand_mul`, `coeff_map` and the polynomial-to-series map.
The [mathematical conclusion and evidence](https://github.com/the-omega-institute/trureturing/issues/30449#issuecomment-6880604852)
refer to this complete event.

## Triage

Proved: the complete native event holds for every positive n, every
positive m and every natural k. Integer existence and unrestricted
uniqueness follow from normalized contraction and the forced constant
coefficient one. The substitution U(y)=y*P_n(y^n) converts the equation
to the existing Lagrange interface. Coefficient transport and the A008287
identity then give the stated rational sum. Positivity of N=n*k+m
justifies division and implies k≤3N, including k=0. Both sum endpoints
are included. This is an unbounded symbolic result, with no finite-instance
restriction.

The Scribe result node carries `OpenProblemResolutionClaim` with
`ResolutionKind.Proved`. The proof shape is bind-only; its seven private
auxiliary theorems are consumed by the result. Admission uses the external
named problem exception under
[#30449](https://github.com/the-omega-institute/trureturing/issues/30449),
with no escape witness or new axiom. The public-result escape audit remains
unfinished under
[#30462](https://github.com/the-omega-institute/trureturing/issues/30462);
it is not `declared_validated`.

Unresolved: the source's separate lattice-path and logarithmic conjectures
are outside this result, so no dependent conclusion requiring them is
settled here. The general polynomial equation P=Q(X*P^n), with a suitable
polynomial coefficient supplier, remains an untested successor candidate.
No wider-family resolution or originality claim follows.

## ASSUMED-UNVERIFIED

The standing check is bounded by the surfaces and query limits in
#30449; unavailable MathDB and OpenAlex readings remain unverified.
No exhaustive absence, originality or model diversity is asserted.
The source's separate path and logarithmic
conjectures remain outside this event.
