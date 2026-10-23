---
slug: oeis-a400361-second-order-pillai-floor-gcd
bibkey: oeis2026a400361
doi: null
url: https://oeis.org/A400361
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/A400361SecondTerm
---

# OEIS A400361: the exact second-order cumulative formula

## Problem

Write P(n)=sum_{k=1}^n gcd(n,k), F(n)=sum_{k=1}^n gcd(n,floor(n/k)),
and a(n)=P(n)-F(n), using signed subtraction. The COMMENT conjecture in
revision 17 asks, along all positive integers N, for

$$
\sum_{n=1}^{N}a(n)=\frac{3}{\pi^2}N^2\log N+CN^2+o(N^2),
$$

with the literal constant

$$
C=\frac{3}{\pi^2}\left(-\frac12+2\gamma-
\frac{6\zeta'(2)}{\pi^2}\right)-\frac{\pi^2}{12}
-\frac12\sum_{d\ge1}\frac{\varphi(d)
(\psi(1+1/d)+\gamma)}{d^2}.
$$

The full literal source and attribution are in
[oeis2026a400361](../Library/Asymptotics/oeis2026a400361.md).
The preregistration is [issue 18775](https://github.com/the-omega-institute/trureturing/issues/18775).
The target is first tier, an external OEIS conjecture. Its recent source
version does not imply novelty; the bounded literature scope and remaining
Bu-Xu full-text uncertainty are recorded in the source dossier.

### Native statement

`D5.S3.ArithSums.A400361SecondTerm.originalClaim : Prop` conjoins absolute
summability of the literal real coefficient sequence with little-o of the
exact remainder against N^2 at the natural atTop filter. The theorem
`D5.S3.ArithSums.A400361SecondTerm.result : originalClaim` has no hypotheses.
The definitions preserve the positive source range, integer subtraction,
real Gamma logarithmic derivative, real zeta restriction, and every term
of the source constant. Normalizing the remainder by N^2 is proved
equivalent to the stated little-o. No subsequence or finite proxy is used.

## Motivation

The exact source formula isolates the joint divisor and quotient relation in
F(n). The defining second-order constant is fixed before the asymptotic
analysis, so identifying its literal convergent series is part of the problem.

## Gap

The classical Pillai mean is established prior mathematics. The required
delta is the exact floor-gcd mean and its convergent digamma/totient
coefficient, combined with the original full unrestricted source assertion.
No equivalent whole prior was established in the actually inspected scopes;
Bu-Xu full-text overlap remains unknown, and no global novelty is asserted.

## Route

### Floor-gcd derivation

Expand gcd by the sum of totients over common divisors. With n=d*m, the
condition floor(d*m/k)=d*ell is exactly m=k*ell+r and d*r<k. The edge r=0
contributes floor((N/d)/ell). For r>0 put k=d*r+j. The remaining exact
count is the positive lattice triangle

$$
(d\ell+1)r+\ell j\le\lfloor N/d\rfloor,\qquad r,j\ge1.
$$

The normalized triangle count tends to 1/(2*ell*(d*ell+1)). Uniform bounds
by 1/(A*B) for triangle parameters A,B provide a summable two-index
majorant after totient weighting. The edge sum is the sigma prefix, whose
normalized limit is pi^2/12. Summing the interior limits gives

$$
\lim_{N\to\infty}\frac{\sum_{n=1}^N F(n)}{N^2}
=\frac{\pi^2}{12}+\frac12\sum_{d\ge1}
\frac{\varphi(d)(\psi(1+1/d)+\gamma)}{d^2}.
$$

The reciprocal kernel for psi includes d=1 and proves the series convergence.
Every floor equality and strict upper boundary is kept in the exact bijection.

### Classical Pillai contribution

The original Pillai totient divisor formula is reused from its owning
module. The identity phi*zeta=id and Mobius inversion express the Pillai
prefix as the Mobius convolution of the weighted divisor-pair prefix
W(N)=sum_{a*b<=N} a*b. The exact symmetric hyperbola split at floor(sqrt(N))
gives W(N)/N^2-log(N)/2 tending to gamma-1/4. Domination by reciprocal
squares and log(2d)/d^2 transfers the residual and logarithmic terms.
The quotient-square defect is at most 2/(N*d); the remaining reciprocal
square tail is at most 1/N. Hence the extra log(N) factor leaves a vanishing
rounding error. Differentiating zeta(s)*L_mu(s)=1 at two yields the exact
Mobius logarithmic moment 36*zeta'(2)/pi^4 and the classical Pillai constant.
This classical result receives no separate open-problem credit.

## Triage

`admission_basis: open-problem-resolution`, under issue 18775.
The final declaration has `proof_shape: content`: the exact floor-gcd
lattice decomposition, convergent two-index transfer and literal coefficient
identification are used in its live proof. Private binding lemmas only
organize consumed steps. Utility is none: there is no finite certified
instance, bounded enumeration or computational checker offered as the result.
The newly visible original `pillai_divisors` retains its statement and proof
and has a real new consumer in the full summatory theorem.

### What the settlement shows

The proved mechanism is the exact quotient-fiber decomposition into its
zero-remainder edge and positive lattice triangles. The edge supplies
pi^2/12 and the interior supplies the literal digamma/totient series.
The unrestricted result is `D5/S3/ArithSums/A400361SecondTerm.result`;
the classical Pillai contribution is the live support theorem
`D5/S3/ArithSums/A400361PillaiMean.pillai_second_term`.
An effective error rate, further weights and additional open-problem
settlements are not consequences asserted here.

## Evidence

The native D5 theorem uses precisely the standard axioms
`Classical.choice`, `Quot.sound`, and `propext`. The source-owned Reg
realization retains the entire original conjunction and varies the actual
coefficient-series readout. Its rejected realization is the constant-one
sequence, which is not summable. The actual readout is observationally
nonconstant on positive indices: the coefficient is one at one, and its
summability forces a different value at another positive index. Variation and
sensitivity therefore concern the real summability clause; they do not
infer zero-limit sensitivity from a different ratio-limit theorem.
The original Pillai divisor formula has its own source-owned totient-readout
realization, with its entire nonzero-index telescope and divisor sum.

The shared kernels and classical Pillai mean have source-owned Reg
realizations retaining their complete statements, including the quotient
parameter zero. The kernel and cast readouts have actual finite variation.
For the Pillai mean, adding n to P(n) changes the normalized prefix by a
quantity tending to 1/2 and therefore rejects the original law. This is
sensitivity of the actual second-term statement, with positive dependence
witnesses P(1) and P(2).

## Falsifier

A different limit for the same normalized remainder along an unbounded
positive-index sequence would contradict the theorem. A finite discrepancy
in sequence terms would require checking the source definitions but would
not alone refute an asymptotic statement. Effective rates, a certified
decimal value of C, and generalizations to other floor-gcd weights are not
proved here. No exhaustive literature or publication-priority claim is made.

## ASSUMED-UNVERIFIED

The mathematical theorem assumes no unproved premise or extra axiom.
Literature clearance is bounded: the unavailable Bu-Xu full text has not
been checked, and no exhaustive publication-priority assertion is made.
