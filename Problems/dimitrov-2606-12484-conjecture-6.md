---
slug: dimitrov-2606-12484-conjecture-6
bibkey: dimitrov2026c6
doi: null
url: https://arxiv.org/abs/2606.12484v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovLowerBoundC6.result
---

# Dimitrov's Conjecture 6

## Problem

For all integers $n\geq2$ and $k\geq1$, put $a=\varphi(n)^k$,
$b=\psi(n)^k$ and $c=\sigma(n)^k$. The exact original statement is

$$
\frac{ab}{c(a+b)}+\frac{ac}{b(a+c)}+\frac{bc}{a(b+c)}
\geq\frac{4(n-1)^{2k}+(n^2-1)^k+(n+1)^{2k}}
{2((n-1)^{2k}+(n^2-1)^k)}.
$$

The functions are Euler's totient, Dedekind psi and the positive-divisor sum;
all displayed arithmetic is over the reals and powers are pointwise powers of
function values. The source is arXiv:2606.12484v1, Conjecture 6. The complete
external endpoint and its bounded literature screen are preregistered in
[#30478](https://github.com/the-omega-institute/trureturing/issues/30478).

## Motivation

This is the original sixth conjecture, with unrestricted source quantifiers.
Theorem 4 is only its exponent-one case; Conjecture 3 has a different bound.

## Gap

The source labels this statement a conjecture. The bounded source and duplicate
screen supplied in #30478 found no exact prior settlement in its checked scope.
This does not establish worldwide absence of a proof or historical priority.

## Route

Apply the existing complete `DimitrovLowerBoundsC4C5.result5`. For the positive
source powers, the reciprocal product of $a(b+c),b(a+c),c(a+b)$ equals six plus
twice the present left side. Its right side equals six plus twice the present
right side. Exact field normalization and a linear inequality finish the proof.
No private exposure or new analytic inequality is required.

## Falsifier

An exact violating integer pair $n\geq2$, $k\geq1$ would refute the original
statement. A failed proof attempt or a finite computation is not a refutation.

## Evidence

The candidate declaration is `DimitrovLowerBoundC6.result : DimitrovLowerBoundC6.claim`.
It directly consumes frozen `DimitrovLowerBoundsC4C5.result5`; the complete source
formula is retained in `claim`. The result has `proof_shape: bind-only` and
`escape_witness: none`; its candidate admission basis is `open-problem-resolution`.
The mirrored `Reg/D5/S3/Arith/Divisors/DimitrovLowerBoundC6.lean` supplies the
source-equivalence bridge, whole-family variation, sensitivity and actual
observational dependence for the totient family, with continuation unknown.

## Triage

The mathematical application covers the complete original range. Post-door
independent evaluation, required CI, merge and first dev verification remain
delivery obligations. No KPI or novelty credit is asserted by this dossier.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the supplied source census. Worldwide
priority and exhaustive literature coverage are unverified.
