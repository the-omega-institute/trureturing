---
slug: mathar-2011-a165433-recurrence
bibkey: mathar2011a165433
doi: null
url: https://oeis.org/A165433
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatharA165433.result
---

# Mathar's recurrence for OEIS A165433

## Problem

OEIS A165433, FORMULA field, revision 17 (unpaginated), defines

$$
a(n)=\sum_{k=0}^{\lfloor n/2\rfloor}
\binom{n-k}{k}\frac{(2k)!}{k!\,2^k}.
$$

Its conjecture line states:

> Conjecture: 2*a(n) -3*a(n-1) +(3-2*n)*a(n-2) +(2*n-3)*a(n-3)=0. - _R. J. Mathar_, Nov 14 2011

The complete formal assertion is

$$
\forall n\in\mathbb N,\quad 3\le n\Longrightarrow
2a(n)-3a(n-1)+(3-2n)a(n-2)+(2n-3)a(n-3)=0.
$$

The sum includes both endpoints. The binomial coefficient and factorials
are evaluated in the naturals and cast to the rationals before division.
The power of two, products, quotient, sum and recurrence arithmetic are
rational; the coefficient variable is the rational cast of n. Every index
subtraction is natural subtraction. The source has offset 0,3 and specifies
no recurrence onset; n>=3 is the full domain using only nonnegative
predecessor indices. There is no upper index bound, analytic premise,
eventual-only qualification, integrality assumption, natural-division
reinterpretation or replacement sequence.

## Motivation

The recurrence constrains every value of the literal source sum. It resolves
the named recurrence assertion without assuming that an alternative
double-factorial formula or a recurrence-defined sequence equals that sum.

## Gap

The source snapshot labels this recurrence a conjecture. The bounded source
qualification and library search attached to
[issue #27279](https://github.com/the-omega-institute/trureturing/issues/27279)
did not identify an existing supplier of the complete literal assertion.
The pinned Mathlib binomial and factorial identities supply the proof
ingredients. This is a not-found-in-searched-scope finding; worldwide
openness and priority are unverified.

## Route

Write t(n,k)=binomial(n-k,k), b(k)=(2k)!/(k!*2^k), and

$$
T(c,n)=\sum_{k=0}^{n}t(n,k)c(k),\qquad
W(c,n)=T(k\mapsto k c(k),n),
$$

in the rationals. The binomial coefficient vanishes for n<2k.
Pascal's identity and the multiplicative binomial identity give

$$
T(c,n+2)=T(c,n+1)+T(k\mapsto c(k+1),n),
$$

$$
(n+1)(T(c,n+1)-T(c,n))=2W(c,n+1)-W(c,n).
$$

Factorial successors and cancellation of nonzero rational denominators give
b(k+1)=(2k+1)b(k), hence

$$
T(k\mapsto b(k+1),n)=2W(b,n)+T(b,n).
$$

Eliminating the shifted transforms and weighted sums from the two Pascal
relations and these identities yields the required recurrence at n+3.
Terms above floor(n/2) vanish, proving T(b,n)=a(n) for the entire literal
inclusive sum. Every natural index at least three has the form n+3.

## Falsifier

A natural index n>=3 where the displayed rational sum violates the recurrence
would contradict `D5/S1/Recurrence/MatharA165433.result`.

## Evidence

The mathematical source is `D5/S1/Recurrence/MatharA165433.lean`.
Its complete public surface is `a`, `claim`, and `result`; the named theorem
has exactly type `claim`. Its axiom closure is limited to `Classical.choice`,
`Quot.sound`, and `propext`. The local transform identities are proof
components, with no additional top-level mathematical helpers or exported
resolution claims. The Blueprint attaches its typed `Proved` resolution
to this result; the sourced definitions retain literature provenance.

The independent
[exact-event evaluation](https://github.com/the-omega-institute/trureturing/issues/27279#issuecomment-6685374124)
accepted this unchanged assertion at 2026-11-06T12:59:15Z, before its original
2026-11-06T13:00:00Z deadline. The
[terminal](https://github.com/the-omega-institute/trureturing/issues/27279#issuecomment-6685381515)
and
[canonical research readout](https://github.com/the-omega-institute/trureturing/issues/27279#issuecomment-6685400392)
remain the settlement of that event. The predecessor
[issue #27220](https://github.com/the-omega-institute/trureturing/issues/27220)
remains unresolved, with its original prediction and settlement unchanged.
Mathematical settlement does not certify merged delivery or a KPI increment.

## Triage

Tier 1 external named OEIS conjecture. Admission basis is
`open-problem-resolution`, with
[the exact preregistration](https://github.com/the-omega-institute/trureturing/issues/27279#issuecomment-6684719047).
The result's proof shape is `bind-only`: it applies pinned Mathlib binomial,
factorial and finite-sum identities, support bounds, casts and normalization.
There is no escape witness or direct frozen D5 mathematical predecessor.
Utility is `none`. This resolution claims no new general proof technique.

### What the settlement shows

- **Proved:** the exact literal rational sum satisfies the recurrence for
  every natural n>=3.
- **Proved within that result:** the full-range transform equals the original
  sum, and the weighted-transform identities eliminate to the recurrence.
  These are proof components, not separate named resolutions.
- **Unresolved here:** integrality, alternative sequence definitions,
  generating-function and asymptotic claims, and neighboring conjectures.
  Extension below three would require a separate statement about indices.
- **Source boundary:** no assertion about every other formula in A165433 or
  dependencies of other open problems follows from this resolution.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive absence of earlier proofs remain
unverified beyond the bounded source qualification and library search.

The information-escape audit is unfinished under
[the concrete source audit issue](https://github.com/the-omega-institute/trureturing/issues/27279#issuecomment-6685063611).
The retained typed Reg mirror compiles, including its realization equivalence,
whole-family variation/sensitivity and observational-dependence proof terms.
Its producer record is `declared_unresolved`:
`IE-C050 ClosedTruthReadout`, `unclassified_form`, `source.roles`.
A classified source-role binding and its full source-bound certificate are
missing. There is no `declared_validated` certificate. The explicit
`.unknown` continuation records only an unknown residual and asserts neither
undecidability nor inexhaustibility. Mathematical kernel verification and
the typed resolution claim do not complete this audit.
