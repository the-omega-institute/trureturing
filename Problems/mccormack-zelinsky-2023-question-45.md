---
slug: mccormack-zelinsky-2023-question-45
bibkey: mccormackzelinsky2023weightedamgm
doi: 10.48550/arXiv.2312.11661
url: https://arxiv.org/abs/2312.11661v4
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.result
---

# The weighted totient condition D1 is strong among Euler forms

## Problem

McCormack and Zelinsky, arXiv:2312.11661v4, page 19:

> Similarly, let D1 be the statement “n is pseudoperfect with some S1 where A(S1, n) ≤ C(S1, n).”
> Question 45. Is D1 a strong property, a weak property, or neither?

A positive integer is pseudoperfect if some subset of its positive proper
divisors sums to it. An S1 is a subset of its positive divisors, possibly
including n, with sum 2n. Equations (12) and (14) define

$$
A(S,n)=\sum_{d\in S}\frac{d}{2n}\log\varphi(d),\qquad
C(S,n)=\log\left(\sum_{d\in S}\frac{\varphi(n/d)}{2d}\right).
$$

The predicate D1 retains both the independent pseudoperfect condition and
existence of S1 satisfying A <= C. Neither inclusion of 1 nor closure under
complementary divisors is required.

The Euler set and counting notation are defined on pages 18--19:

> Given a set of natural numbers S, we will write S(x) as the number of elements in S which are at most x.
> Euler proved that if n is an odd perfect number, then n = q^s m^2 for some prime q, where q ≡ s ≡ 1 (mod 4), and where (q, m) = 1. Let E be the set of all numbers of that form.
> Given a statement S we will write E_S to be the set of elements of E which satisfy S.
> The second author defined a property S to be a weak property if
> lim_{x→∞} E_S(x)/E(x) = 1.
> Motivated by this, the second author said that S is a strong property if
> lim_{x→∞} E_S(x)/E(x) = 0.

The quotations use linear notation for the displayed formulas. The existing
`EulerForm` faithfully expresses this set: n = q^s m^2 with q prime,
q % 4 = s % 4 = 1, m positive and gcd(q,m)=1. It imposes no oddness
condition on m. Both counts use 1 <= n <= X and count integers once,
regardless of how many representations they have. The exact conclusion is

`Tendsto (fun X : Nat => (eulerD1Count X : Real) / eulerCount X) atTop (nhds 0)`.

Thus D1 is a strong property. Real thresholds reduce to natural floors.
The definition of `Pseudoperfect` does not impose positivity at zero;
zero is excluded by both counting intervals.

## Motivation

A strong necessary condition excludes a proportion tending to one of the
Euler-form candidates for odd perfect numbers. Ordinary natural density
among all integers does not answer this relative-density question.

## Gap

The weighted inequality involves an arbitrary divisor subset, without the
complementary symmetry used for strongly pseudoperfect numbers. Its analytic
sign must first give a restriction usable in a uniform count.

## Route

For a prime q and r >= 1, D1(qr) implies q <= sigma(r), without any
coprimality assumption. If q > sigma(r), let U be the elements of S1 not
divisible by q. Each divides r, so their sum u is less than q. The total
sum is 2qr, and all remaining terms are divisible by q; hence q divides u.
Thus u=0 and every element of S1 is divisible by q.

Write S1=qT with T a nonempty subset of the divisors of r. The identity
sum over e dividing r of phi(r/e)=r then gives

$$
0<\sum_{d\in S1}\frac{\varphi(qr/d)}{2d}
\le\frac{r}{2q}<1.
$$

Consequently C<0, whereas positive divisors have positive totient and A>=0.
This contradicts A<=C.

When s=1, q <= sigma(m^2) <= m^4. The existing small-square image bound
is sharper than the T^5 estimate: square factors m<=T contribute at most
3T^3. Large square factors contribute at most 2X/(T+1) by the existing
reciprocal-square count. For s>=5,
write s=5+4j and absorb q^(2j) into m; the existing high-power image bound
is at most sqrt(X). Taking T=floor(X^(1/6)) gives the bound below when
X^(1/6)>=2. For smaller X, the elementary bound E_{D1}(X)<=X gives
the same conclusion:

$$
E_{D1}(X)\le4X^{5/6}\quad(X\ge1).
$$

Every prime congruent to one modulo four is an Euler form, with s=m=1.
The existing lower bound gives E(X)>=exp(-50)X/log(X) eventually.
The ratio is bounded by 4exp(50)log(X)/X^(1/6), which tends to zero.

## Falsifier

Dropping the independent pseudoperfect condition, imposing complementary
closure on S1, or imposing oddness of m would change the statement.
Real.log must only be declared negative after establishing strict positivity
of its argument. The prime obstruction must not assume coprimality.
Image bounds do not require uniqueness of Euler representations.

## Evidence

The exact Lean statement is `WeightedTotientEulerDensity.result`.
The source definitions, prime obstruction and explicit count are its proof
components. The resolution is preregistered in #31746. The literature assessment
there covered the question number, authors, title, D1, pseudoperfect, totient, strong property
and density, and found no resolution. Wang and Zelinsky's subsequent work
on strongly pseudoperfect numbers does not address D1. This bounded search
is not an exhaustive priority certification.

## Triage

- **Proved in Lean:** the sign obstruction D1(qr) implies q<=sigma(r),
  even without gcd(q,r)=1. The pseudoperfect clause is preserved, although
  the obstruction only uses the S1 witness and weighted inequality.
- **Proved in Lean:** the numerator is at most 4X^(5/6) for X>=1;
  the denominator is eventually at least exp(-50)X/log(X).
- **Source comparison:** Question 44's relative-density result does not
  imply this one. D1 does not require S1 to be complementary-divisor closed.
- **Proved on paper:** restricting to E_odd, with m odd, gives the same
  limit: its numerator has the same upper bound, and primes still give
  the same denominator lower bound. The larger-set limit alone would
  not imply this assertion. No separate Lean theorem is asserted for it.
- **Not settled here:** Question 34 on page 14 of the source, which asks
  for an odd primitive non-deficient n that is pseudoperfect with a set S1
  containing 1 and satisfying A(S1, n) > C(S1, n). The relative-density
  theorem does not classify individual divisor sets or settle that question.
- **Proved on paper:** the sign-obstruction lemma does not use the
  pseudoperfect conjunct, so the same counting shows that Euler forms
  admitting any divisor set S with sum 2n and A(S, n) <= C(S, n) are
  relatively sparse. The Lean theorem is stated for D1 only.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive subsequent literature coverage are
unverified. The E_odd version has the paper proof stated above.
