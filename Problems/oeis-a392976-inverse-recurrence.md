---
slug: oeis-a392976-inverse-recurrence
bibkey: mathar2026a392976
doi: null
url: https://oeis.org/A392976/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/A308815DFiniteRecurrence.euler_coeff
---

# Mathar's A392976 inverse recurrence and D-finiteness

## Problem

OEIS A392976, revision 19, January 31, 2026, gives Manyama's sequence and
Mathar's conjecture in these literal NAME and FORMULA lines:

```text
%N A392976 Expansion of (1/x) * Series_Reversion( x * ((1-x^2)^2 - x) ).
%F A392976 Conjecture D-finite with recurrence 283*n*(n-1)*(n-2)*(83022305213*n -178385058984)*(n+1) *a(n) -6*n*(n-1)*(n-2)*(12196786904129*n^2 -45110300936020*n +52641391340361)*a(n-1) -6*(n-1)*(n-2)*(67790996421377*n^3 -248299346995054*n^2 +202497447227007*n +3061418504418)*a(n-2) -2*(n-2)*(192167357944360*n^4 -559010679688491*n^3 -2120668219560541*n^2 +9123363136130610*n -8342981628089220)*a(n-3) +5*(15640122296875*n^5 -565964885220500*n^4 +4989857715427325*n^3 -18667678380008380*n^2 +32085126156301848*n -20925325629575136)*a(n-4) +10*(5*n-17)*(5*n-18) *(5*n-21)*(5*n-19)*(22509687685*n-60308240636)*a(n-5)=0. - _R. J. Mathar_, Jan 29 2026
```

The fixed event is the conjunction of D-finiteness and this exact identity
for every integer n at least five. Five is the complete valid-lag
interpretation, not an author-quoted start index. The sequence offset is
zero; the secondary offset three is not an onset.

The Lean definition `f` is the polynomial in the quoted reversion. `U` is
its zero-constant formal compositional inverse over Q. The complete `claim`
requires its constant coefficient to vanish, both compositions to equal X,
and every zero-constant formal right inverse to equal U. It also requires
X times A to equal U. The coefficient a(n) equals the coefficient of degree
n+1 in U, so A is the original offset-zero ordinary generating series.
Rationals are the characteristic-zero coefficient carrier of the published
integer sequence; no analytic branch replaces the formal inverse.

`DFinite A` requires a natural derivative bound d and polynomials indexed by
Fin(d+1), at least one nonzero, whose homogeneous linear combination of the
formal derivatives of A is zero. The final conjunct of `claim` is exactly
the six signed terms of the quotation, with signs +---++ and lags zero
through five. Natural indices n at least five represent every integer in
that range; sequence-argument subtraction has no negative case there.
No exceptional index is removed and no eventual-only claim is substituted.

## Motivation

A general algebraic-series D-finiteness theorem would establish only one
part of the event. The named question also requires the exact operator
encoded in Mathar's coefficients to annihilate the generating series
constructed from the original inverse. The frozen Euler coefficient
identity in `D5/S1/Recurrence/A308815DFiniteRecurrence.euler_coeff` connects
operator annihilation to the required all-index coefficient identity.

## Gap

The source labels the joint assertion a conjecture. The bounded source,
repository public/private, pinned Mathlib and third-party qualification in
[issue #28023](https://github.com/the-omega-institute/trureturing/issues/28023)
identified reusable inverse and coefficient machinery but no supplier of the
whole literal assertion. The corresponding Library note records the checked
scope and source attribution. This finding does not certify worldwide
openness, priority or exhaustive absence of an earlier proof.

The result below closes the exact mathematical event. Its source-occurrence
escape audit remains unfinished under the distinct issue linked below.

## Route

The proof constructs U using Mathlib's formal substitution inverse, proves
both inverse identities and uniqueness, and defines A by shifting U's
coefficients down by one degree. All subsequent operators act on these same
formal series.

`wA` stores the six signed coefficient polynomials. The Euler operator theta
is X times the formal derivative. `wU` shifts the Euler argument to transport
the operator from A to U using X times A equals U. After composition with f,
the chain rule expresses the transported iterates using powers of H, the
derivative of f. H has constant coefficient one, permitting denominator
clearing and cancellation in the formal power series ring. The retained
polynomial certificate reduces the resulting numerator to zero.

`A_operator` transports that polynomial identity back to A. `coeff_op` and
`recurrence` extract coefficients at an arbitrary n at least five, retaining
all six lagged terms. `normal_form` expands the Euler powers into ordinary
formal derivatives; `dfinite` provides the homogeneous order-five
polynomial-coefficient operator. Its fifth-derivative coefficient polynomial
has coefficient 23495312375279 at degree five, so the operator is nonzero.
`result` combines these facts with the original inverse and uniqueness
clauses. This is a symbolic identity for the entire formal series, rather
than a finite initial-segment check.

## Falsifier

A zero-constant formal right inverse different from U, failure of either
composition, failure of X times A equals U, a nonzero coefficient of the
proved annihilating expression, or an integer n at least five violating any
coefficient or sign in the literal recurrence would contradict
`D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.result`.
A finite agreement test alone cannot establish this universal conclusion.

## Evidence

The mathematical source is
`D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.lean`.
Its public objects are `f`, `U`, `A`, `a`, `DFinite` and `claim`; its sole
external resolution endpoint is the closed theorem `result : claim`.
No hypothesis assumes either the recurrence or D-finiteness. The canonical
Blueprint binds `OpenProblemResolutionClaim(Proved)` for this dossier to
that exact theorem. The accepted axiom boundary is `propext`,
`Classical.choice` and `Quot.sound`; no new or private axiom is supplied.

The direct frozen provider is the Euler coefficient theorem identified in
Motivation, with statement identity
`sha256:099f203a01661739a74345c59aab6ffbe85f72fa99d109ccf4a4458f343096ce`.
The inverse construction, composition/uniqueness laws, differential rules
and coefficient interfaces are reused from pinned Mathlib. The other
sequence's recurrence endpoint is not a supplier of this event.

## Triage

Tier 1 external named recent OEIS conjecture. The admission basis is
`open-problem-resolution` under the exact
[preregistered full event](https://github.com/the-omega-institute/trureturing/issues/28023#issuecomment-6719559027).
All 23 authored D5 theorem proofs are `bind-only` under expansion of helpers,
definitions and normalization against the existing frozen and pinned
upstream ingredients. Every helper has an actual proof consumer; `result`
is the single external settlement endpoint. There is no escape-witness
claim. Utility is `none`: the retained result is a universal formal-series
identity; symbolic polynomial normalization serves its proof, and no
standalone finite positive sequence instance is retained.

### Proved mechanism and neighboring boundaries

- **Proved by `result`:** both inverse compositions, uniqueness among all
  zero-constant formal right inverses, X times A equals U, homogeneous
  nonzero D-finiteness, and every one of the six literal recurrence terms
  at every integer n at least five.
- **Mechanism used inside this result:** chain-rule transport through f,
  denominator clearing by its unit derivative, a polynomial identity,
  and arbitrary-index coefficient extraction. The order-five operator's
  explicit nonzero coefficient establishes D-finiteness. These internal
  steps are not additional exported problem resolutions or a new general
  algorithm.
- **Open in this delivery:** minimal differential order, minimal recurrence
  order, parameterized inverse-polynomial families, analytic asymptotics,
  and any independent integrality or combinatorial interpretation theorem.
  The existing certificate asserts none of these generalizations.
- **Source boundary:** only the full quoted conjecture is settled. No proof
  of every other formula in A392976, or dependency of another named open
  problem on this one, is asserted. The all-index proof does not depend on
  numerical initial-segment agreement.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive absence of earlier proofs remain
unverified beyond the bounded qualification above.

The compiling retained mirror
`Reg/D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.lean` has an unfinished
source-binding audit, disclosed in
[issue #28047](https://github.com/the-omega-institute/trureturing/issues/28047).
Its inspector state is `declared_unresolved`, with diagnostic
`IE-C050 ClosedTruthReadout reason=unclassified_form rule=source.roles`:
`Signature.Role` is Unit, while `sourceSelection.readouts` selects six
recurrence occurrences. Faithful occurrence/role/actual-observation
correspondence and successful whole-source reconstruction are missing;
later observation and reconstruction checks are not established by the
first diagnostic. The original theorem telescope, typed family bridge,
positive law, variation/sensitivity and observational-dependence proofs are
retained. A compiling client is not `declared_validated`, and unknown
continuation proves no undecidability. This issue is audit disclosure,
not mathematical evidence.
