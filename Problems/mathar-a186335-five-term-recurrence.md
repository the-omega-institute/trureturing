---
slug: mathar-a186335-five-term-recurrence
bibkey: mathar2015a186335
doi: null
url: https://oeis.org/A186335
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.result
---

# Mathar's five-term recurrence for OEIS A186335

## Problem

OEIS A186335, NAME “A transform of the central binomial coefficients”,
FORMULA revision 11, defines

$$
a(n)=\sum_{\substack{0\le j\le k\le n\\
 m=n-k-j\ge0,\ m\le k-j}}
\binom{k-j}{m}\binom{k}{j}\binom{2m}{m}.
$$

The entry's conjecture, attributed to R. J. Mathar, is

> Conjecture: n*a(n) +(-2*n+1)*a(n-1) +5*(-n+1)*a(n-2) +3*(2*n-3)*a(n-3) +5*(n-2)*a(n-4)=0.

Precisely, for every natural number $n\ge4$ the integer relation is

$$
na(n)+(1-2n)a(n-1)+5(1-n)a(n-2)
+3(2n-3)a(n-3)+5(n-2)a(n-4)=0.
$$

Both finite-sum endpoints are included. Binomial arguments are natural
numbers and every summand is cast to the integers. The legal support
requires $j\le k$, $k+j\le n$ and $n-k-j\le k-j$ before interpreting
natural subtraction. Excluded terms contribute zero; the central-binomial
sequence is never evaluated at a negative index. The source offset is zero;
it omits the recurrence onset and negative-index convention. The stated
support and complete domain $n\ge4$ are the explicit interpretation of
those omissions. The same assertion holds for integer indices $n\ge4$
under the usual identification with natural indices.

## Motivation

The relation controls every index of the independently defined source sum.
It connects a finite combinatorial transform to a polynomial differential
equation for its entire formal generating series, without an analytic
convergence assumption.

## Gap

The exact source conjecture is qualified in
[issue #30472](https://github.com/the-omega-institute/trureturing/issues/30472).
The bounded source and literature reading recorded in
`Library/RecurrenceAlgebraic/mathar2015a186335.md` identified general methods
but no exact supplier of the complete A186335 statement. This is a finding
within the recorded search scope, not exhaustive absence of earlier proofs.

## Route

Reindex the legal pairs by $m=n-k-j$ and $j$, with inverse $k=n-m-j$.
The exact transformed support is $2m+2j\le n$. Binomial multiplication
and coefficient identities for powers of
$B=(1-X-X^2)^{-1}$ identify the source series with

$$
A=B\,C(X^2B),\qquad
C=\sum_{m\ge0}\binom{2m}{m}X^m\in\mathbb Q[[X]].
$$

The substitution argument has zero constant coefficient. This identity is
derived from the finite source sum. The central-binomial equation
$(1-4X)C'=2C$, inverse differentiation and the formal chain rule give

$$
PA'+QA=0,\qquad
P=1-2X-5X^2+6X^3+5X^4,\quad
Q=-1-5X+9X^2+10X^3.
$$

Coefficient extraction through
`D5/S1/Recurrence/A308815DFiniteRecurrence.euler_coeff`, followed by the
four coefficient shifts, yields exactly the five signed integer terms.
The generating-function identity is proved rather than assumed; neither
a finite prefix nor a recurrence-defined substitute supplies the sequence.

## Falsifier

A natural index $n\ge4$ where the original legal-pair double sum violates
the displayed integer relation would contradict
`D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.result`.
An error in the source-to-series correspondence would invalidate that
claimed correspondence, rather than license replacing the source sum.

## Evidence

The mathematical source is
`D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence.lean`.
Its sole public theorem `result` proves `claim` for the sequence `a`
defined by `sourcePairs`. The 18 retained theorem proofs include the
private reindexing, kernel coefficient, source-identification, differential
and recurrence-extraction steps. Those helpers are used on the derivation
path to `result`. The accepted axiom boundary is `Classical.choice`,
`Quot.sound` and `propext`.

The source bibliographic key is `mathar2015a186335`, with canonical URL
https://oeis.org/A186335. The corresponding Blueprint attaches its
`Proved` resolution claim to the frozen `result` declaration.

## Triage

This is the complete universal resolution of the named external recurrence,
with `proof_shape: bind-only`, `admission_basis: open-problem-resolution`
and `utility: none`. The decisive mechanism is the exact finite-sum
reindexing and formal substitution, followed by differential coefficient
extraction. It does not claim a new general coefficient-extraction theorem.

### What follows and what remains open

- **Proved:** the five-term relation holds for the original legal-pair
  double sum at every index $n\ge4$, with no additional premise.
- **Internal consequences:** the source generating-series identity and its
  polynomial differential equation are steps of that proof, not additional
  exported problem resolutions.
- **Unresolved here:** parameterized versions of the transform, a general
  characterization of coefficient weights admitting this mechanism,
  minimal recurrence order and analytic asymptotics. The differential
  certificate does not settle these questions.
- **Neighbor boundary:** no sibling OEIS conjecture is resolved by this
  declaration, and no dependency of another named open problem on this
  recurrence is established within the recorded source scope.
- **Prior-literature boundary:** Mathar's arXiv:2109.02112v1 and the inspected
  Ekhad–Yang–Zeilberger proof output and SCHUTZENBERGER tables supply
  methods; the bounded reading identified no exact A186335 settlement.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive literature coverage remain
unverified. Individual historical OEIS snapshots and reliable general
web-search coverage were unavailable within the recorded qualification.

The four-slot Reg source-binding audit remains unfinished under
[issue #30498](https://github.com/the-omega-institute/trureturing/issues/30498)
and [issue #21914](https://github.com/the-omega-institute/trureturing/issues/21914).
The retained Reg mirror proves full-law kernel obligations but does not
provide an accepted source-binding certificate: the Nat.mod source-operand
audit and corresponding binding evidence remain unresolved. This is not
`declared_validated`; kernel verification of the recurrence does not
discharge the missing audit obligations.
