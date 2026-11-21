---
slug: defant-2014-powerful-solitude-conjecture-4-1
bibkey: defant2014abundancy
doi: 10.48550/arXiv.1506.05416
url: https://arxiv.org/pdf/1506.05416v1#page=23
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.result
---

# Defant’s Conjecture 4.1 on powerful solitude

## Problem

Colin Defant, *An Extension of the Abundancy Index to Certain Quadratic Rings*,
Conjecture 4.1, arXiv:1506.05416v1, p. 23 (journal p. 81), states the following.
[Source PDF](https://arxiv.org/pdf/1506.05416v1#page=23)

> Let $d\in K$. If $p$ is an integer prime and $k$ is a positive integer,
> then $p^k$ is $n$-powerfully solitary in $\mathcal O_{\mathbb Q(\sqrt d)}$
> for all positive integers $n$.

Here $K=\{-163,-67,-43,-19,-11,-7,-3,-2,-1\}$ and integer primes are
positive. Solitude means that every nonzero element with the same $I_n$ has
the same absolute value.

## Motivation

The Norton threshold result for Beri–Zelinsky Question 6 concerns ordinary
integer abundancy. Defant’s conjecture asks about solitude after extending
the index to quadratic integers, where a rational prime can have two
nonassociated conjugate prime factors.

## Gap

The bounded literature check identified partial cases in the source and
found no prior settlement of the full claim in the material examined.
[Preregistration #32039](https://github.com/the-omega-institute/trureturing/issues/32039)

## Route

Use $d=-11$, $p=3$, $k=1$ and $n=2$. Put $\pi=(1+\sqrt{-11})/2$, so
$\pi^2=\pi-3$, and compare $3$ with $w=7\pi-3$. For a nonzero sector element
$u$, divisibility of $z$ is equivalent to divisibility of both integral
coordinates of $z\bar u$ by $N(u)$. The norm bound puts both complete divisor
sets inside $[-15,11]\times[0,7]$, a box of 216 points. Their norm lists, with one entry
per sector divisor, are $(1,9,3,3)$ and $(1,9,3,5,45,15,27,135)$.
At $n=2$ the divisor weights are the norms. Their sums are $16$ and $240$,
so $I_2(3)=16/9=240/135=I_2(w)$. The squared absolute values are $9$ and $135$.

## Falsifier

The witness requires complete sector-divisor sets and two different absolute
values. An omitted divisor, a spurious divisor, or a mismatch between the
source sector and the coordinate test would invalidate the corresponding
calculation.

## Evidence

| Source clause | Lean counterpart and correspondence |
| --- | --- |
| The nine radicands and the rings in §1 | `d ∈ K` lists exactly those nine values. `R d` uses the basis $1,\omega$ with $\omega=\sqrt d$ or $(1+\sqrt d)/2$ according to $d\bmod 4$. The relation for $\omega^2$ determines both parameters of `QuadraticAlgebra`. |
| Absolute value and the half-open sectors in §2 | `absoluteValue` takes the square root of $z\bar z$. In the basis $1,\omega$, `A` uses $x>0, y\ge0$ for the sectors $[0,\pi/2)$ at $d=-1$ and $[0,\pi/3)$ at $d=-3$. The other seven sectors are $[0,\pi)$, given by $y>0$ or $y=0, x>0$. |
| Definitions 2.1 and 2.2 | `delta` sums $\lvert u\rvert^n$ over actual divisors in `A`, one per associate class, using the integer exponent. `I` divides by $\lvert z\rvert^n$ with natural $n$. Positive norms bound the coordinates of divisors, giving finite support. |
| Positive rational prime, positive power and all positive exponents | `p : ℕ` and `Nat.Prime p` give the source prime. `0 < k` and `0 < n` are explicit, and `primePower d p k hp` casts $p^k$ into `R d` as a nonzero element. |
| Solitude in the whole ring | `claim` quantifies over every `z : Nonzero d` and denies `PowerfullyFriendly`, which is equality of indices together with inequality of absolute values. |

The compiled declarations in `D5/S3/Arith/Abundancy/DefantC41Settlement.lean`
have literal types `claim : Prop` and `result : Not claim`. The axiom closure
is `Classical.choice`, `Quot.sound` and `propext`. The module has zero direct
frozen dependencies. Its `certified-instance` utility has basis `refutes`,
with `claim` as the target and `result` as the designated refutation under
§3.9. There are no other new public theorems or lemmas requiring Reg.

## Triage

Tier 1 external conjecture, preregistered in #32039. The admission basis is
`open-problem-resolution`. The proof shape of `result` is `content`, using
integral quotient reconstruction and two complete divisor certificates.

### What the settlement shows

The counterexample proves that the split rational prime $3=\pi\bar\pi$ can
have a friend at even exponent $n=2$. The factorization
$w=-\pi^3(1+\pi)$ puts all three factors above $3$ on the $\pi$ side, and
$N(1+\pi)=5$. These different divisor patterns produce equal normalized sums.
The source’s ring-prime-power theorem and its odd-$n$ cases retain their
stated scope. [Theorem 2.2(e), Theorem 3.2 and Corollary 3.2](https://arxiv.org/pdf/1506.05416v1)

## ASSUMED-UNVERIFIED

The compiled statement covers the full rational-prime-power conjecture.
The stronger question in the next sentence of the paper concerns products
of powers of a ring prime and its conjugate. Exhaustive literature coverage
and publication priority remain unverified.
