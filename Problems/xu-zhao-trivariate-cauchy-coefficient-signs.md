---
slug: xu-zhao-trivariate-cauchy-coefficient-signs
bibkey: xu2026rational
doi: 10.48550/arXiv.2609.11072
url: https://arxiv.org/html/2609.11072v1
triage: window
motivation_gids:
  - D5/S3/Weil/Probability/AnalyticLogarithmicContinuation
---

# Xu-Zhao Conjecture 1.3

## Problem

For every nonempty positive composition $k=(k_1,\ldots,k_d)$ and integer
$\ell\ge1$, put $F_k(z)=z^{-d}\operatorname{Li}_k(z)$ with its removable
value at zero, and
$C_n^{j;k;\ell}=[z^n](1-z)^{-j}F_k(z)^{-\ell}$ as in source equations
(7)-(8). Conjecture 1.3 asks for $C_n^{0;k;\ell}<0$ eventually. For every
fixed integer $j\ge1$ it also asks for $C_n^{j;k;\ell}>0$ eventually and,
if $k_1>1$, for
$C_n^{j;k;\ell}>\binom{n+j-1}{n}/\zeta(k)^\ell$ eventually.
The threshold may depend on $k,\ell,j$; the strict inequality and all
quantifiers are retained.

## Motivation

The frozen scalar-series analyticity supplier connects polynomial
coefficient bounds with the actual analytic generating series. The
composition disk theorem now supplies a noncircular source-specific
analytic reciprocal on the entire unit disk, needed before its Taylor
coefficients can be identified with the source's formal inverse.

## Gap

`CompositionZeroFree.result` is only the intermediate all-composition disk
theorem: absolute convergence, analyticity, nonvanishing, and positive
real part of the extended logarithmic derivative. Both source recurrences,
strict-index correspondence and exact zero order are established in its
dependency unit. The full conjecture is not proved and receives zero
solved-problem credit; there is no `OpenProblemResolutionClaim`.

`CompositionSlit.result` additionally constructs the actual all-composition
branch on the full slit domain, proves holomorphy, disk agreement, origin
normalization, exact depth-order vanishing, conjugation symmetry and both
origin-correct recurrences. It assumes no continuation or recurrence premise
and asserts no global slit nonvanishing. This is also an intermediate with
zero solved-problem credit.

Admissible boundary convergence, uniform power-log bank
expansions, a fixed zero-free slit collar, formal-inverse/Taylor coefficient
identity, and the finite-contour sign transfer remain unproved here.
The eventual sign and strict binomial conclusions therefore remain open
in this repository. Preregistration:
https://github.com/the-omega-institute/trureturing/issues/9372.

## Route

After the disk unit, prove the remaining source-specific analytic bridges
and the negative upper-bank sign. A finite contour gives eventual strict
negativity. Eventual negativity together with the actual finite radial
limit yields absolute summability: bound finite sums with radial weights
first, then pass to radius one. Strict negative tails give the $j=1$
excess. A uniform positive radial lower bound gives eventually positive
partial sums, and repeated summation handles every fixed $j\ge2$.
No coefficient asymptotic equivalent or boundary derivative total is
assumed in this route.

## Falsifier

A positive composition and power with infinitely many nonnegative
$C_n^{0;k;\ell}$, or a fixed positive $j$ with infinitely many failures of
its required strict inequality, refutes the conjecture. A disk zero of
the actual normalized series would instead contradict the intermediate
formal theorem; replacing that series by a surrogate would test a
different object.

## Evidence

The Lean unit is `CompositionDisk.lean`, `CompositionRecurrences.lean`
and `CompositionZeroFree.lean` under
`D5/S3/AnalyticClosure/Polylogarithm/`. Its final declaration is
`CompositionZeroFree.result : CompositionDisk.diskStatement`.
The consumer quantifies only over a positive head and a list of positive
tail entries; no analytic recurrence or zero-free premise is supplied.
The explicit extension has $Q(0)=d$, and the zero of `li` has order exactly
$d$ with positive minimal-tuple leading coefficient. The companion
Library notes record source correspondence and classical attribution.

## Triage

`window`: the complete conjecture remains the target. The source settles
all-one compositions for every $\ell\ge1$ by the all-one identity and
Theorems 1.1 and 8.2; depth one and depth two at $\ell=1$ by Theorems 9.6
and 9.9, respectively; and depth one at $\ell=2$ by Corollary 9.11.
The present disk and slit results are intermediates, not a new resolution
of those known cases or of the full conjecture. Admission uses the actual
source-specific escape content, not the open-problem-resolution exception.

## ASSUMED-UNVERIFIED

Worldwide unresolved status and priority are not established by the
bounded literature assessment. The first-contact argument is classical,
and no novelty claim is attached to it. Independent semantic review and
caller-owned admission/CI remain separate from the kernel compilation.
