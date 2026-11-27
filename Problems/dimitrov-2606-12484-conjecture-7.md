---
slug: dimitrov-2606-12484-conjecture-7
bibkey: dimitrov2026c7
doi: null
url: https://arxiv.org/abs/2606.12484v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovPairSumC7.result
---

# Dimitrov's Conjecture 7

## Problem

S. I. Dimitrov, *Lower bounds on expressions depending on the functions
φ(n), ψ(n) and σ(n), III*, arXiv:2606.12484v1, §2, PDF page 4,
Conjecture 7, asks whether for every integer $n\ge2$ and every integer
$k\ge1$, with

$$
x=\varphi(n)+\psi(n),\qquad y=\varphi(n)+\sigma(n),\qquad
z=\psi(n)+\sigma(n),
$$

one has

$$
\frac{x^k}{y^k+z^k}+\frac{y^k}{x^k+z^k}+\frac{z^k}{x^k+y^k}
\ge
\frac{4n^{2k}+(n+1)^{2k}+n^k(n+1)^k}
{2\bigl(n^{2k}+n^k(n+1)^k\bigr)}.
$$

Here $\varphi$ is Euler's totient, $\psi$ is Dedekind's function, and
$\sigma$ is the sum of all positive divisors. The entire pair sums are
raised to $k$, all quotients are over the reals, and the quantifiers are
unrestricted. The source is [arXiv:2606.12484v1](https://arxiv.org/abs/2606.12484v1),
Conjecture 7.

## Motivation

This is the source's seventh conjecture with its full $n\ge2$, $k\ge1$
range. The endpoint retains the actual arithmetic functions and the source's
powered pair sums; the exponent is not moved inside an individual function
value or pair sum.

## Gap

The bounded literature comparison found no prior complete resolution in
Dimitrov Parts I–IV (Part IV DOI 10.3390/math14213935), Sándor–Gryszka III,
the public Lean donor
`pro20541/dimitrov-conjectures-lean` at
`95809b59deefd8dfad81e398250aedd7e1aea3b3`, or the available citation and
duplicate searches. [#30579](https://github.com/the-omega-institute/trureturing/issues/30579)

## Route

For $n\ge2$, set $q=(n+1)/n$.
Totient positivity and the public `DimitrovLowerBoundsC4C5.psi_ge` and
`sigma_ge_psi` give $0<x\le y$.
The first projection of `DimitrovPsiSigmaSeparation.separation` gives
$1<q\le z/y$. Raising positive quantities to $k$ preserves order, and
$y>0$ gives $(z/y)^k=z^k/y^k$. Thus $1<q^k\le z^k/y^k$ and
$0<x^k\le y^k\le z^k$.
The first projection of `DimitrovNesbittOppositeGap.opposite_gap` with
$X=x^k$, $Y=y^k$, $Z=z^k$, $s=q^k$ gives the lower bound
$q^k/2+2/(1+q^k)$, which normalizes to the displayed right-hand side.
The [Library note](../Library/ArithUnits/dimitrov2026c7.md#consumed-lean-suppliers)
records the two source declarations and the attribution for C4/C5.

## Falsifier

An exact integer pair $n\ge2$, $k\ge1$ violating the displayed inequality
would refute the original statement. A finite computation, a restricted
exponent range, or a failed proof attempt is not a refutation.

## Evidence

The mirrored registration in `Reg/D5/S3/Arith/Divisors/DimitrovPairSumC7.lean`
uses the Euler-totient family, with continuation unknown. The rendered Scribe
document and compiled D5 and Reg artifacts are available. Verification of the
current Reg binding is pending.
[Scribe document](../Blueprint/D5/S3/Arith/Divisors/DimitrovPairSumC7.md)

## Triage

**Proved.** `D5/S3/Arith/Divisors/DimitrovPairSumC7.result` proves
`DimitrovPairSumC7.claim` with real ratios for all natural numbers $n\ge2$
and $k\ge1$. At $k=1$ the pair sums are unpowered and the right side becomes
$(6n^2+3n+1)/(2n(2n+1))$, recovering
[Part III, Theorem 5](https://arxiv.org/html/2606.12484v1#Thmtheorem5).

At $k=0$ and $n\ge2$, outside the Lean endpoint, all powered terms are $1$.
The left side is $3/2$ and the right side is $(4+1+1)/(2(1+1))=3/2$.
At $n=1$, the three functions equal $1$, so $x=y=z=2$ and the left side is
$3/2$ for every $k$. With $t=2^k$, the right side is $t/2+2/(1+t)$.
It equals $5/3$ at $k=1$ and exceeds $3/2$ by $(t-1)^2/(2(1+t))>0$ for
every $k\ge1$.

For prime $n$, $\varphi(n)=n-1$ and $\psi(n)=\sigma(n)=n+1$. Hence
$x=y=2n$ and $z=2(n+1)$, and the left side equals
$2/(1+q^k)+q^k/2$, attaining the bound for every $k\ge1$.

**Equality classification, deduced from the supplier projections.** On the
source range, $s=q^k>1$, so the second projection of `opposite_gap` forces
$x^k=y^k$ and $z^k=q^k y^k$ at equality. Since $u\mapsto u^k$ is strictly
increasing on positive reals for $k\ge1$, $(z/y)^k=q^k$ implies $z/y=q$.
The second projection of `separation` makes this ratio equality equivalent
to primality. Thus equality in the stated bound holds exactly at primes.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources and repository states named
in #30579. Some forward-citation indexes were inaccessible, including the
OpenAlex citing-work query. Exhaustive coverage and publication priority
are unverified.
