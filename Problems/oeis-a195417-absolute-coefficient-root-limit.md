---
slug: oeis-a195417-absolute-coefficient-root-limit
bibkey: hanna2011a195417
doi: null
url: https://oeis.org/A195417/internal
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Polynomial/A195417RootLimit
---

# The complete absolute coefficient root limit in OEIS A195417

## Problem

Paul D. Hanna and the OEIS contributors, A195417, author line Sep 17 2011;
entry revision 11, Jan 05 2023 04:41:38:

> a(n) = sum of the absolute values of the coefficients in (1+x-x^3)^n.
>
> What is the limit a(n)^(1/n)? The limit appears to be near 2.657...

Let p=1+X-X^3 in Z[X]. For every natural n, including zero, set

$$
a(n)=\sum_{j=0}^{3n}|[X^j]p^n|.
$$

The question asks for the exact full natural-index limit of
(a(n):R) raised to the real power 1/(n:R). Absolute values are taken
coefficient by coefficient before summation. The adjacent question about
successive ratios and their attractors is separate.

## Motivation

The complete coefficient l1 norm measures the total size of all signed
coefficients. Its exponential growth need not equal the signed coefficient
sum. An exact limiting constant answers the first explicit source question.

## Gap

The bounded source qualification in
[issue 27845](https://github.com/the-omega-institute/trureturing/issues/27845)
identified no exact settlement among the inspected repository, pinned
Mathlib, third-party Lean, public issues and published catalog. The source
entry asks the question without supplying an answer. General spectral-radius
and Wiener-algebra principles are established prior mathematics and are
not new claims here. No directly corresponding theory volume was identified.
The bounded search does not establish worldwide openness or priority.

## Route

Put s=sqrt(13), C=(97+26s)/27 and M=sqrt(C). On the unit circle, u=Re(z)
satisfies -1<=u<=1 and

$$
|1+z-z^3|^2=5+8u-4u^2-8u^3,\qquad
C-(5+8u-4u^2-8u^3)=\frac{(6u+1-s)^2(6u+1+2s)}{27}.
$$

The latter expression is nonnegative since s>=5/2. Equality is attained
at u=(s-1)/6 and z=u+i sqrt(1-u^2), which has norm one. Thus M is the
exact maximum modulus of p on the unit circle.

Evaluation gives M^n<=a(n). Coefficient maps and the degree bound identify
the original integer sum with the complex support norm sum. The original
A192205RootLimit.power_sum_sq_le uses finite Fourier Parseval and
Cauchy-Schwarz to give a(n)^2<=(3n+1)M^(2n), hence
M^n<=a(n)<=(3n+1)M^n. For n>=1 the real nth root is squeezed between M
and (3n+1)^(1/n)M. The original A192205RootLimit.degree_root_limit makes
the extra factor tend to one.

## Falsifier

Failure of convergence to this exact radical along natural indices would
refute the proposed answer. A finite prefix, the source decimal, a limsup,
a ratio limit or the absolute value of the signed sum cannot establish
this full coefficientwise root limit.

## Evidence

The Lean source is D5/S3/Analytic/Polynomial/A195417RootLimit.lean.
Its definitions p and a retain the original integer polynomial and the
complete coefficientwise natural absolute sum, including a(0)=1. The
unconditional theorem result states

$$
\lim_{n\to\infty}(a(n):\mathbb R)^{1/(n:\mathbb R)}
=\sqrt{\frac{97+26\sqrt{13}}{27}}.
$$

The exponent uses real rpow. The lower bound directly reuses
CountableHankelNegativeWitness.eval_bound; the upper bound and limiting
factor directly reuse the original A192205 declarations. Their statements
and proofs are preserved. No finite calculation substitutes for convergence.

## Triage

Proved: the complete first A195417 root-limit question with exact radical,
all natural indices, coefficientwise absolute values and real rpow. The
unit-circle maximum and two-sided bounds are proved as consumed helpers.
The general Fourier and root-squeeze mechanism is established mathematics;
the named external application is the result presented here.

Computed: no numerical estimate is used as proof of the limit. The source's
approximate decimal receives no separate resolution credit.

Open: the adjacent ratio-limit and attractor questions remain outside this
result. No further external question or successor theorem is asserted.
The inspected primary entry identifies no dependent result relying on this
root limit. Applying the mechanism to another polynomial would require its
own coefficient correspondence and exact unit-circle maximum.

## ASSUMED-UNVERIFIED

Worldwide openness and first-publication priority are not established by
the bounded source screen. The live OEIS JSON definition and question were
verified; the internal-page endpoint returned HTTP 403. MathDB proxy
first-page searches and unavailable private code search do not exclude
unindexed or unpublished settlements. The OEIS entry is attributed to
Hanna and the OEIS contributors under CC-BY-SA-4.0.
