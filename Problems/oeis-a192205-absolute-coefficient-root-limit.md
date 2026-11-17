---
slug: oeis-a192205-absolute-coefficient-root-limit
bibkey: hanna2011a192205
doi: null
url: https://oeis.org/A192205/internal
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Polynomial/A192205RootLimit
---

# The complete absolute coefficient root limit in OEIS A192205

## Problem

Paul D. Hanna and the OEIS contributors, A192205, author line Jun 25 2011;
inspected internal-page snapshot revision 16, Aug 01 2013 18:16:08:

> a(n) = sum of absolute values of coefficients in (1-x-x^2+x^3)^n.
>
> Conjecture: limit a(n)^(1/n) = 16*sqrt(3)/9 = 3.079201..., which is substantiated by the observation that the sums of the coefficients squared in (1-x-x^2+x^3)^n equals binomial(4n,n) (cf. A005810).

Let p=1-X-X^2+X^3 in Z[X]. For every natural n, including zero, set

$$
a(n)=\sum_{j=0}^{3n}|[X^j]p^n|.
$$

The standalone assertion is the full all-natural limit

$$
\lim_{n\to\infty}(a(n):\mathbb R)^{1/(n:\mathbb R)}
=\frac{16\sqrt3}{9}.
$$

The exponent uses real rpow. The binomial observation is source context,
not an assumed identity or a second resolution.

## Motivation

This named external conjecture asks for the exponential growth rate of
the complete coefficient l1 norm of powers of a fixed signed polynomial.
Cancellation makes the signed coefficient sum a different observable.
The full coefficient sum, the integer coefficients and the all-index
limit are essential parts of the question.

## Gap

The inspected primary entry labels the limit a conjecture. Bounded
qualification in [issue 27758](https://github.com/the-omega-institute/trureturing/issues/27758)
found no exact settlement among the inspected repository, private D5,
pinned Mathlib, third-party Lean, public issues and published catalog.
It did identify the established general Wiener/Gelfand principle and
finite Fourier suppliers. Those known methods are reused; they are not
claimed as a new general theory or as proof of global priority.
No directly corresponding theory volume was identified in that scope.

## Route

Factor p(z)=(1-z)^2(1+z). On the unit circle put u=Re(z); then
|p(z)|^2=8(1-u)^2(1+u). Its difference from 256/27 is
8(3u+1)^2(5-3u)/27, which is nonnegative for u<=1. Equality is
attained at z=-1/3+(2*sqrt(2)/3)i. Thus M=16*sqrt(3)/9 is the
maximum modulus.

Evaluation at this point gives M^n<=a(n). The integer coefficient sum
is identified with the complex support norm sum using coefficient maps,
the degree bound and zero extension. Parseval and Cauchy-Schwarz give
a(n)^2<=(3n+1)M^(2n), hence a(n)<=(3n+1)M^n. For n>=1,
real nth roots lie between M and (3n+1)^(1/n)M. The latter factor
tends to one, proving the full limit by squeezing.

## Falsifier

A failure of the stated epsilon definition along natural indices would
refute the conjecture. A finite prefix or agreement with the displayed
decimal cannot prove it. Replacing the sum of coefficient absolute values
by the absolute value of the signed sum changes the problem and supplies
no evidence for this assertion.

## Evidence

The mathematical source is
`D5/S3/Analytic/Polynomial/A192205RootLimit.lean`. Its definitions p and a
encode the integer polynomial and the complete per-coefficient natural
absolute sum. The public theorem result has no additional hypotheses and
states the displayed full real-rpow limit. In particular a(0)=1, and the
support correspondence includes both indices zero and 3n.

The lower estimate uses the original
`CountableHankelNegativeWitness.eval_bound`, which bounds polynomial
evaluation on the closed unit disk by the coefficient absolute sum.
The upper estimate uses pinned Mathlib's
`Polynomial.sum_sq_norm_coeff_eq_circleAverage` and finite
Cauchy-Schwarz. The existing root-asymptotic supplier and squeeze theorem
complete the argument. No squared-coefficient binomial identity is used.

## Triage

Proved: the exact complete A192205 root-limit assertion, with real rpow,
all natural indices and no coefficient sign assumptions. The proof also
derives the displayed lower and upper estimates as consumed private steps.
The finite Fourier, Parseval, Cauchy-Schwarz and root-squeeze mechanism is
established mathematics; the delivered result is this named application.

Computed: no finite calculation is used as a substitute for the limit proof.
The source decimal and binomial observation receive no separate resolution
credit.

Open: the source's squared-coefficient binomial observation is not proved
here. A192210 is a separate preregistered question and is not resolved here.
No dependent result or follow-up claim relying on this conjecture was
identified in the inspected primary entry. The same coefficient-norm
mechanism for other fixed polynomials would still require their own
coefficient correspondence and unit-circle maximum; no further external
question is settled here.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish worldwide openness or
first-publication priority. The separately rendered revision-16 body,
original Gelfand/Wiener papers and proposed lecture labels were not
verified. Attribution rests on the retained primary internal-page snapshot
and its independently checked source reading. A fresh live-page retrieval
was not verified (HTTP 403); external endpoint restrictions limit the
bounded search. The entry is cited under CC-BY-SA-4.0.
