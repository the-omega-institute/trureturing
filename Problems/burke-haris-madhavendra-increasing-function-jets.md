---
slug: burke-haris-madhavendra-increasing-function-jets
bibkey: burkeharismadhavendra2025repeatedintegrals
doi: 10.48550/arXiv.2512.02151
url: https://arxiv.org/abs/2512.02151v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.result
---

# The all-order increasing-function endpoint-jet assertion

## Problem

Maxim R. Burke, Maleeha Haris and Madhavendra, *Repeated integrals of increasing
functions*, arXiv:2512.02151v1, Conjecture 1.2, p. 2:

> $(P_n)$ is true for all nonnegative integers $n$.

For each $n\geq 0$, let $W_n\subseteq\mathbb R^{n+1}$ consist of vectors
$b=(b_0,\ldots,b_n)$ for which some $f\in C^n[0,1]$ has nondecreasing,
nonconstant $D^n f$ and satisfies $D^j f(0)=0$ and $D^j f(1)=b_j$ for every
$0\leq j\leq n$. Here $D^0f=f$ and endpoint derivatives are one-sided.
Nondecreasing does not mean strictly increasing, and absolute continuity is
not an input hypothesis.

The assertion $(P_n)$ requires both openness of $W_n$ and, for every $b\in W_n$,
one function $F\in C^\infty[0,1]$ satisfying all of the following:

- $D^jF(0)=0$ and $D^jF(1)=b_j$ for every $0\leq j\leq n$;
- $D^{n+1}F(x)>0$ for every $0<x<1$;
- $D^{n+1}F(0)=D^{n+1}F(1)=1$;
- $D^jF(0)=D^jF(1)=0$ for every $j>n+1$.

The sole problem anchor is this original Conjecture 1.2, including $n=0$.
The follow-up arXiv:2512.23949v1 calls the same interval property $Q_n$ and
retains its all-order assertion as Conjecture 2.5.

## Motivation

The source's Theorem 8.2 proves only $n=0,1,2,3$. The conjecture asks whether
every attainable finite endpoint jet admits one simultaneous smooth
realization, with the specified strict interior sign and full endpoint
conditions, at every order. The follow-up uses the interval assertion in
conditional comonotone entire-function approximation and interpolation results.

## Gap

The bounded preregistration screen in
[issue 12872](https://github.com/the-omega-institute/trureturing/issues/12872)
reports no exact published all-order settlement in the inspected primary and
follow-up versions, author/title arXiv queries, a comonotone-function query,
and a Crossref title query. Those are attributed literature-screen results,
not an exhaustive absence or priority claim.

Di Dio's arXiv:1804.07058v2, DOI 10.1090/proc/14499, gives related moment-cone
and mixture methods. It does not state the original endpoint-one and
all-higher-zero assertion. The mathematical relation needed here includes
singular continuous input derivatives and exact simultaneous moments, rather
than only approximate moments or an absolutely continuous input class.

## Route

Represent the continuous, nondecreasing highest input derivative by its
Stieltjes measure after clamping to $[0,1]$. Nonconstancy gives positive mass;
continuity gives atomlessness. Triangular integration identifies the endpoint
jets with reversed factorial moment coordinates of
$\gamma_n(t)=((1-t)^k)_{k=0}^n$. Strict separation, together with the finite
zero set of a nonzero polynomial, places that moment vector in the interior
of the moment cone.

Normalized smooth densities, positive on $(0,1)$ and flat at both endpoints,
concentrate at every center in $[0,1]$, including the two endpoints. Their
moment cone has full affine span. The convex-interior and closure argument
therefore supplies exact finite nonnegative mixtures for interior moments;
it uses no assumption that such a point lies inside a full-dimensional simplex
of the original generating curve.

Add a small smooth endpoint correction with value one at both endpoints.
Its moment vector tends to zero, so the residual remains in the cone interior
and admits one exact mixture. Integrating the resulting density $n+1$ times
constructs a single function with every required jet. The inverse coordinate
map also identifies the attainable jet set with the preimage of the cone
interior and yields openness.

## Falsifier

An order $n\geq0$ at which $W_n$ is not open, or an attainable vector with
no single smooth function satisfying all four endpoint and positivity clauses,
would refute the original assertion. A restriction to finitely many orders,
strict input monotonicity, absolute continuity, or approximate moment matching
would fail to establish this problem's statement.

## Evidence

The mathematical source is
[OriginalIncreasingFunctionJets.lean](../D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.lean).
Its public theorem `PnOriginal.result` has the exact statement
`∀ n : ℕ, PnOriginal.P n`. The definitions `PnOriginal.W` and `PnOriginal.P`
encode the complete source input class and both conclusions, using
`iteratedDerivWithin` on the closed unit interval for the one-sided endpoint
convention. The corresponding
[Blueprint](../Blueprint/D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.md)
displays these definitions and the all-order theorem.

## Triage

`theorem`; Tier 1, the specific finite-jet interpolation conjecture
preregistered in issue 12872. The mathematical result is an analytic
existence and openness theorem, rather than a bounded enumeration, numerical
certificate, or positive finite instance.

### What the settlement shows

- **Proved**, by `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.result`:
  the original $(P_n)$ holds for every $n\geq0$, retaining weak monotonicity,
  nonconstancy, singular continuous and flat input cases, openness, and one
  witness satisfying all the finite and higher endpoint jets simultaneously.
  The decisive mechanism in its proof is exact interior moment realization
  after a small compensated endpoint correction, followed by repeated
  integration. No additional regularity hypothesis on the input is required.
- **Literature-level consequence**: the follow-up's equivalent $Q_n$ interval
  assertion is supplied at every order. Results conditional on that assertion
  retain their other hypotheses. Their entire-function approximation and
  interpolation conclusions are not additional formalized conclusions of
  `PnOriginal.result`.
- **Open here**: a separate theorem for independently prescribed next-order
  endpoint values or arbitrary infinite endpoint germs, quantitative bounds
  on mixture size or concentration width, and a formal bridge to the
  follow-up's global entire-function results. None is asserted by the
  displayed result; each would require its own faithful statement, reuse
  search, and proof obligation.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources and queries reported in
issue 12872. OpenAlex and Semantic Scholar rate-limited that screen; Google
Scholar and DuckDuckGo challenged automated access. No worldwide literature
completeness or originality claim follows. The published equivalence with the
follow-up's notation and its global conditional consumers is used only as
ordinary source context; those bridges and consumers are not Lean theorems
of this module. The original all-order interval assertion is the full scope
of the resolution claim.
