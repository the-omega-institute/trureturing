---
slug: mathar-2011-a117187-recurrence
bibkey: mathar2011a117187
doi: null
url: https://oeis.org/A117187/internal
triage: theorem
motivation_gids:
  - D5/S3/Constants/Moments/A117187MatharRecurrence
---

# Mathar's literal A117187 recurrence

## Problem

The Online Encyclopedia of Integer Sequences, A117187, defines the sequence by:

> Expansion of (1+x)c(x^2)/((1-x^2*c(x^2))sqrt(1-4x^2)), c(x) the g.f. of A000108.

Its FORMULA field states:

> Conjecture D-finite with recurrence: (n+4)*(31n-12)*a(n) +(37n^2+24n-156)*a(n-1) -4*(31n^2+81n+24)*a(n-2) -4*(37n+24)*(n-1)*a(n-3) =0. - R. J. Mathar, Dec 10 2011

Let C be the standard Catalan series over the integers, let S be the
constant-one square root of 1-4X², and set

F=(1+X)C(X²)/((1-X²C(X²))S), a(n)=[Xⁿ]F.

Division uses the genuine two-sided inverse of the displayed unit denominator.
The target is the printed recurrence for every natural n≥3, including n=3.
The source prints no onset; three is the complete nonnegative-lag domain.
No analytic convergence, finite cutoff, or recurrence-defined replacement
sequence is assumed.

## Motivation

This first-tier named OEIS conjecture asks for an exact recurrence of an
algebraic generating function. A full-series identity and parity reduction
connect the literal source to existing Catalan derivative coefficients.
The question concerns the printed assertion, not the novelty of a general
recurrence-generation method.

## Gap

The bounded prior-work inspection found the equivalent coefficient formula
in LODA, a different holonomic program in jOEIS, a finite-prefix/program
equivalence benchmark, the A001791 shifted formula and adjacent recurrence,
and the A117184 triangle. The inspected Ekhad–Yang–Zeilberger catalogue and
Mathar paper provide general methods but no located complete certificate
for this exact source-to-recurrence statement. These are bounded findings,
not exhaustive absence or priority claims. The Library note gives exact
versions, attribution and the source-text hash. Preregistration is
[issue #30252](https://github.com/the-omega-institute/trureturing/issues/30252).

## Route

The Catalan equation gives S=1-2X²C(X²), S²=1-4X² and constant coefficient
one. In the integral-domain ring of integer formal series, equality of
squares and the constant coefficient distinguish S from -S, proving
uniqueness among all integer formal series with this normalization.
The denominator has constant coefficient one and a two-sided inverse.

The existing Catalan differential identity
X(1-4X)C′+(1-2X)C=1 is applied through the injective coefficient map
from integer to rational formal series. Together with C²X+1=C it gives
C′(1-2XC)=C² and C²(1-XC)=C. Substitution and unit cancellation yield
the entire identity F=(1+X)C′(X²), not a prefix comparison.

The existing derivative coefficient identity then gives
a(2m)=a(2m+1)=b(m), where b(m)=binomial(2m+2,m).
Adjacent binomial identities imply

E(m)=m(m+2)b(m)-2(m+1)(2m+1)b(m-1)=0 for m≥1.

For the printed residual R, polynomial normalization yields

R(2m+1)=272E(m) for m≥1,

mR(2m)=4(31m-6)E(m)+4(37m+12)E(m-1) for m≥2.

These two cases cover all n≥3, with the odd case including n=3.
The nonzero integer m can be cancelled in the even case.

## Falsifier

A nonzero printed residual at any n≥3 would refute the claimed recurrence.
A mismatch in the literal generating function, Catalan series, normalization,
inverse, coefficient extraction, cast or lag would invalidate the source
correspondence. A finite prefix cannot establish the full conclusion.
An existing complete proof of the exact target would remove the basis for
retaining a duplicate application as a new external-problem resolution.

## Evidence

`D5/S3/Constants/Moments/A117187MatharRecurrence.result` includes the
normalized-root characterization and uniqueness, the denominator's unit and
two inverse laws, the complete source-series bridge and the recurrence
for every natural n≥3. It directly reuses
`A331474HankelBridge.source_moments.1` and
`A308815DFiniteRecurrence.cat_ode`; the original generating-function
consumer of the provider remains applicable.
The full result and its six necessary private helpers are applications
of existing mathematics; no new coefficient formula, adjacent identity
or abstract method is asserted.

Quoted source text is attributed to Paul Barry, R. J. Mathar, the OEIS
Foundation and contributors, under CC BY-SA 4.0. The Library note links
the sequence and pinned OEIS EULA and distinguishes independently authored
exposition and Lean from quoted OEIS material and cited program code.

## Triage

Proved by the formal result: the decisive structure is the full Catalan
derivative bridge and duplication of each derivative coefficient in the
even and odd positions. The printed residual vanishes by the existing
adjacent-binomial identity in both parity classes. No finite-prefix or
asymptotic argument is needed, and no extra hypothesis is placed on the
source sequence.

Known prior mathematics: the binomial formula and shifted adjacent
recurrence already occur in the cited sources. They are reused rather
than counted as new conclusions. The bounded entry reading identifies
no additional source-stated conclusion whose validity depends on the
conjecture. No claim about other OEIS recurrences follows from this result.

## ASSUMED-UNVERIFIED

Global priority and openness outside the inspected sources remain
unverified. The individual historical revision-9 endpoint returned
HTTP 403; no retrieval of that snapshot is claimed. The source-bound
audits for the result and exposed provider theorem remain unresolved
under the linked-issue exception in #30252; typed law and variation
proofs do not supply the missing raw-source certificate. Their unknown
continuations are not claims of undecidability. Publication and
external-problem KPI credit are not asserted by this dossier.
