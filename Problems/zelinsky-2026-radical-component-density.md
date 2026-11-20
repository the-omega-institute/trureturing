---
slug: zelinsky-2026-radical-component-density
bibkey: zelinsky2026smallcomponent
doi: 10.48550/arXiv.2005.12115
url: https://arxiv.org/abs/2005.12115v5
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.result
  - D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.result
---

# Radical component density and primitive non-deficient intersections

## Problem

Joshua Zelinsky, *Must a Primitive Non-Deficient Number Always Have a Small
Component?*, Journal of Integer Sequences 29 (2026), Article 26.4.3,
arXiv:2005.12115v5, section 3, pages 9–10:

> Let B be the set of numbers satisfying p_i^{a_i+1} < 2R for all i.

Here n is the product of p_i^{a_i} and R=rad(n).

> Note that B has natural density zero.

> Given a set S, we write S(x) = |{n ∈ S, n ≤ x}|. It seems natural to ask for an asymptotic for
> B(x).

> Let C be the set of primitive non-deficient numbers. Let C_O be the set of odd primitive non-
> deficient numbers.

> Conjecture 10. lim (B ∩ C)(x)/B(x) = 0.

> Conjecture 12. lim (B ∩ C_O)(x)/B(x) = 0.

> Let M be a set of primes, and let C_M be the set of primitive non-deficient numbers which do not
> have any element of M as a prime divisor.

> Conjecture 14. Let M be a non-empty finite set of primes. Then lim (B ∩ C_M)(x)/B(x) = 0.

Primitive non-deficiency means non-deficiency together with deficiency of
all positive proper divisors. Counts use positive integers and inclusive
natural bounds X. The convention at n=1 changes no asymptotic.

## Motivation

The radical component condition constrains every complete prime-power
component against the product of distinct prime factors. Its frequency
determines the denominator in the three conjectures. A positive density
for B lets the density-zero property of C control every stated intersection.

## Gap

The components at repeated primes need separate control from the largest
prime factor. For C, bounded prime powers give only a finite exception;
one must control the remaining near-threshold values of sigma(n)/n
without assuming independence between different prime divisors.

## Route

For lam>0 put

$$
B_{\mathrm{lam}}=\{n\ge2:
 p^{v_p(n)+1}<\mathrm{lam}\,\operatorname{rad}(n)\text{ for every }p\mid n\}.
$$

Let P(n) be the greatest prime factor and
F_c={n≥2:P(n)²<c n}. Each integer outside F_1 has the unique form n=p m,
where p is prime and 1≤m≤p. Thus its inclusive count is exactly

$$
\sum_{p\le\sqrt X}p+
\sum_{\sqrt X<p\le X}\left\lfloor\frac Xp\right\rfloor.
$$

The first term is at most sqrt(X) pi(sqrt(X))=o(X).
The error in replacing the floors in the second term by X/p is at most
pi(X)=o(X). Mertens' reciprocal-prime estimate gives

$$
\sum_{\sqrt X<p\le X}\frac1p\longrightarrow\log2.
$$

Consequently F_1 has density 1−log2. If c>0, the difference between F_c
and F_1 lies in a fixed multiplicative shell a n≤P(n)²≤b n, with
a=min(1,c)>0 and b=max(1,c). Write n=p m. The shell has
p≤sqrt(bX) and m≤p/a, so its count is o(X). Every F_c therefore has the
same density.

The square decomposition n=b²a, with a squarefree, supplies the radical
comparison. Excluding integers with a square divisor b² for b>T costs at
most 2X/(T+1). On the complement b≤T and a divides rad(n), whence
n≤T²rad(n). At a repeated prime, v_p(a)≤1 implies
p^{v_p(n)+1}≤b⁴≤T⁴. At a prime of exponent one the component is p²≤P(n)².
It follows that, once n>T⁶/lam,

$$
F_{\mathrm{lam}/T^2}\setminus\{\text{large square divisor}\}
\subseteq B_{\mathrm{lam}}\subseteq F_{\mathrm{lam}}.
$$

First let X tend to infinity and then T tend to infinity. This proves

$$
B_{\mathrm{lam}}(X)/X\longrightarrow 1-\log2>0
\quad\text{for every lam}>0.
$$

For primitive non-deficient n, deleting a prime factor p from its full
prime power p^e gives

$$
2\le h(n)<2+2/p^e,\qquad h(n)=\sigma(n)/n.
$$

If every full prime power is at most 2L², then n divides (2L²)!, so such
n form a finite exception. Every remaining n has 2≤h(n)<2+1/L².
Fix 2≤K≤L. For those n with a prime p in [K,L] occurring to exponent
one, write n=m p. This map to m is injective: two different primes p,q
with the same cofactor would give h-values separated by at least 1/L²,
since h(m)≥1 and |1/p−1/q|≥1/L². Hence there are at most X/K such n.

The other n either avoid all primes in [K,L] or have a square divisor
p² with p≥K. Put Q equal to the product of the primes in that interval.
Residues modulo Q bound the first count by
X times the product of (1−1/p), plus phi(Q). The second count is at most
2X/K. Mertens' product estimate lets L be chosen so that the interval
product is below 1/K. The upper density of C is therefore at most 4/K
for every K≥2, proving C(X)=o(X).

For every subset C' of C,

$$
0\le\frac{(B_{\mathrm{lam}}\cap C')(X)}{B_{\mathrm{lam}}(X)}
\le\frac{C(X)/X}{B_{\mathrm{lam}}(X)/X}\longrightarrow0.
$$

At lam=2, the choices C'=C, C_O and C_M give exactly Conjectures 10,
12 and 14, including the latter's nonempty finite prime-set quantifier.

## Falsifier

Replacing the denominator B(X) by C(X) changes the problem.
The finite bound X and cofactor m must refer to the same integer in the
injection argument. The squarefree part alone does not bound repeated
components without the bound on b. Strict component inequalities and
prime-power exponents are retained. No numerical trend is used as a proof
of a limit.

## Evidence

`ZelinskyRadicalComponentDensity.result` proves the asymptotic for every
positive lam. `ZelinskyRadicalComponentConjectures.primitive_density_zero`
proves the positive primitive non-deficient count is o(X), using the
existing `ZelinskyZhangDoublePrimitive.PrimitiveNonDeficient` predicate.
`ZelinskyRadicalComponentConjectures.result` gives the three exact
limits. Their `OpenProblemResolutionClaim` is **Proved**.

The source's zero-density assertion for B is contradicted by
`ZelinskyRadicalComponentDensity.result`: its density is 1−log2>0.
The external problem is preregistered in #31907.

Bounded literature scope: the journal version and arXiv v5 state the
three limits as conjectures. Lichtman's 2018 result concerns C rather
than B's asymptotic. Campbell's 2026 counterexamples concern two different
conjectures of Ross (2024), rather than these three statements. The
repository contains no earlier dossier for this radical component density
problem. Exhaustive subsequent literature coverage and worldwide priority
are unverified.

## Triage

- **Proved:** the density of B is controlled by the greatest-prime-factor
  critical set. Repeated-prime components contribute a vanishing tail.
- **Proved:** the source's assertion that B has density zero is false;
  its density is 1−log2.
- **Proved:** the same limit holds for every positive multiplier lam,
  including multipliers below one.
- **Proved:** C has density zero, and all three ratios with denominator
  B(X) in Conjectures 10, 12 and 14 tend to zero.
- **Computed:** 1−log2 is approximately 0.3068528194; this decimal is
  explanatory and is not an input to any proof.
- **Proved separately:** the ratios in Conjectures 11, 13 and 15 have
  denominators C(X), C_O(X) and C_M(X), respectively, and tend to one.
  Their refutations are given in the
  [separate dossier](zelinsky-2026-conjectures-11-13-15.md); they do not
  change the three limits with denominator B(X).

## ASSUMED-UNVERIFIED

The bounded literature assessment does not certify worldwide priority.
No exhaustive literature search or external verification beyond the fixed
source versions and stated scope is asserted.
