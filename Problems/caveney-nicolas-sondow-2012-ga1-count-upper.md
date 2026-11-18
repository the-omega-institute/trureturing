---
slug: caveney-nicolas-sondow-2012-ga1-count-upper
bibkey: caveney2012sacaga
doi: null
url: https://arxiv.org/abs/1112.6010v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/GronwallAbundant/Upper.result
---

# An improved upper bound for proper GA1 numbers

## Problem

Caveney, Nicolas and Sondow, *On SA, CA, and GA numbers*, section 8,
write, with $Q_1(x)$ counting proper GA1 integers at most $x$:

> Q1(x) ≤ exp(c log x / log log x) for some positive c. By estimating the number of good divisors of M ..., it might be possible to improve the above estimate.

A GA1 integer is composite and satisfies $G(N)\ge G(N/p)$ for every
prime divisor $p$, where $G(n)=\sigma(n)/(n\log\log n)$. Properness
requires at least three prime factors counted with multiplicity.
The [source note](../Library/Arith/caveney2012sacaga.md) retains the
supplied definitions, version and exact locators.
The target is bound to [#30595](https://github.com/the-omega-institute/trureturing/issues/30595).

## Motivation

The prime factors of a proper GA1 integer lie below $T=\log N$.
The omitted primes below its largest prime factor consume logarithmic
mass. Quantitative control of $\psi(y)-y$ bounds this mass and hence
the entropy of the omitted-prime set.

## Gap

One strict improvement answering the request in section 8 is the existence of positive constants $a,C$ and a real $x_0$
such that, for every real $x\ge x_0$,

$$
\log(1+Q_1(x))\le C\frac{\log x}{\log\log x}
\exp\bigl(-a(\log\log x)^{1/10}\bigr).
$$

The Lean declaration is `D5.S3.Arith.Robin.GronwallAbundant.result`
in `D5/S3/Arith/Robin/GronwallAbundant/Upper.lean`.
Its statement retains the original counting function, all prime divisors,
and properness with multiplicity. No Riemann hypothesis is an assumption.

## Route

Deleting a prime from a proper GA1 integer leaves an integer at least
four, so both iterated logarithms are positive. The exact local divisor-sum
identity converts the GA1 comparison into a bound on its finite geometric
sum. This is the published CNS Theorem 9 constraint $q^r\le rT$ for every occupied prime-power layer $r\ge1$.
In particular $P(N)\le T$ and a repeated prime satisfies $q^2\le2T$.

Write $E=\sum_{q\mid N}(v_q(N)-1)\log q$ and let $W$ be the sum of
$\log q$ over primes $q\le P(N)$ absent from $N$. Then

$$
T=\theta(P(N))-W+E,\qquad
W\le\psi(P(N))-P(N)+E.
$$

A coarse repetition estimate $E\le72X^{3/4}$ for $T\le X$ suffices.
The quantitative prime number theorem, split at $\sqrt X$, gives a
single bound $W\le CX\exp(-c(\log X)^{1/10})$ for every integer in the
same logarithmic window, including small prime-prefix endpoints.

Encode the integer by its largest prime, the exponents below
$L=\lfloor\sqrt{2X}\rfloor+1$, and its absent large-prime set.
The exponent range $0,\ldots,\lceil2X\rceil$ is sufficient.
Every absent large prime costs at least $\tfrac12\log X$ in $W$.
The encoding is injective by uniqueness of prime factorization.
The elementary weighted-binomial argument bounds the number of absent
sets by $\exp(K(1+\log(M/K)))$. The finite-coordinate cost and repetition
allowance are absorbed into a smaller positive exponential constant.
Finally set $X=\log x$. If $c_0>0$ is the MediumPNT constant, the
proof takes $c=c_0\,2^{-1/10}$ in the uniform budget and
$a=c/2=c_0\,2^{-1/10}/2>0$ in the terminal upper bound.

## Falsifier

A proper GA1 integer violating the prime-power barrier, an equal pair of
codes for distinct admissible integers, or a failed uniform missing-mass
estimate would break the stated route. The target requires an eventual
uniform bound; a finite numerical sample does not establish it.

## Evidence

The mathematical sources are the five modules under
`D5/S3/Arith/Robin/GronwallAbundant/`, with corresponding Blueprint sources.
The quantitative prime input is the existing `MediumPNT` declaration.
The original `PrimeFiberPropagation.sigma_prime_pow_succ`,
`edge_excess` supply the local divisor-sum identity; the latter uses the private
`sigma_mul_prime` internally.
Machine-produced scoped reports and frozen state records determine
compilation and publication status; this dossier does not replace them.

## Triage

The proved mechanism is the same-integer bound $P(N)\le\log N$ together with
missing-prime mass controlled by $\psi(y)-y$.
A lower bound involves the sign oscillations of $\theta(y)-y$
associated with Littlewood and Pintz; the necessary lower-bound bridge
is unresolved here. Under RH, this route suggests a candidate scale for $\log(1+Q_1(x))$ of
$\sqrt{\log x}(\log\log x)^{O(1)}$. That conditional improvement is a
research direction, not a proved result of these modules.

## ASSUMED-UNVERIFIED

The supplied source quotations and bibliographic locators are used as
given; no webpage or PDF was fetched. No worldwide priority claim is made.
No lower counting bound, effective constants, or RH-conditional sharper
upper bound is claimed.
