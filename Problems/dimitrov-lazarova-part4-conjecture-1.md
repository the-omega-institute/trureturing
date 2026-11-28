---
slug: dimitrov-lazarova-part4-conjecture-1
bibkey: dimitrovlazarova2026part4c2
doi: 10.3390/math14213935
url: https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovPartIVC1.result
---

# Dimitrov and Lazarova Part 4, Conjecture 1

## Problem

For all natural numbers $n\geq 2$ and $k\geq 1$, prove

$$
\frac{\varphi(n)^{3k}+\psi(n)^{3k}+\sigma(n)^{3k}}
     {\varphi(n)^k\psi(n)^k\sigma(n)^k}
\geq
\frac{2(n+1)^{3k}+(n-1)^{3k}}{(n+1)^{2k}(n-1)^k}.
$$

The quotients and subtraction are real. Euler's totient is `Nat.totient`.
For nonzero $n$, `OeisA344695GcdSigmaPsiPrimes.psi_prod` identifies Dedekind's
$\psi(n)$ with the product of $p^{e-1}(p+1)$ over exact prime powers $p^e$
dividing $n$. `ArithmeticFunction.sigma_one_apply` identifies
`ArithmeticFunction.sigma 1 n` with the sum of positive divisors.
The publisher states Conjecture 1 in Section 4, page 13, and defines the
functions in Section 1, pages 1–2. The article is licensed CC BY 4.0.
[Library record](../Library/ArithUnits/dimitrovlazarova2026part4c2.md)

## Motivation

Theorem 1 of the source establishes the case $k=1$. Conjecture 1 ranges over
all positive natural exponents and all natural inputs $n\geq 2$.

## Gap

The bounded literature check identified no separate published settlement of
the complete exponent family in its inspected scope. The full statement
and scope are recorded in the original registration and exact reuse unit.
[Predecessor #35004](https://github.com/the-omega-institute/trureturing/issues/35004)
[Exact reuse #35027](https://github.com/the-omega-institute/trureturing/issues/35027)

## Route

Let $a=\varphi(n)$, $b=\psi(n)$, $c=\sigma(n)$, $u=n-1$, and $v=n+1$.
The totient bound and the imported `psi_ge` and `sigma_ge_psi` give
$0<a\leq u$ and $0<v\leq b\leq c$. With $x=(b/a)^k$, $y=(c/a)^k$,
and $r=(v/u)^k$, positivity and monotonicity give $1\leq r\leq x\leq y$.
The original `DimitrovPartFourC4.cubic_ratio_bound` gives
$(1+2r^3)/r^2\leq(1+x^3+y^3)/(xy)$. Exact field normalization identifies
the two sides with the publisher's right and left sides respectively.
The arithmetic bounds retain their existing supplier attribution.
[Supplier and license](../Library/ArithUnits/dimitrov2026c4c5.md)

## Falsifier

A pair of naturals $n\geq 2$ and $k\geq 1$ violating the displayed
inequality with the specified arithmetic functions would refute the conjecture.

## Evidence

`D5/S3/Arith/Divisors/DimitrovPartIVC1.result` proves `claim` with
`propext`, `Classical.choice`, and `Quot.sound`. The proof applies the
original cubic inequality directly and uses the external named open-problem
resolution basis for the exact endpoint. The Scribe records that result
with `OpenProblemResolutionClaim`. The unbounded symbolic result has
`utility: none`.

The owner-mirrored Reg law replaces Euler's totient by one natural-valued
family in both occurrences. The actual family gives exactly `claim`. A
constant-three family fails at $n=2,k=1$, where the left side is $3$ and the
right side is $55/9$. The actual observations differ at $2$ and $3$.

## Triage

The checked Lean module proves the inequality for the full exponent family.
Equality holds exactly when $n$ is prime. For prime $n$,
$\varphi(n)=n-1$ and $\psi(n)=\sigma(n)=n+1$, so $x=y=r$ and the two
normalized quotients coincide. For composite $n$, a proper divisor
$d$ with $1<d<n$ is among $1,\ldots,n-1$ and is excluded from the totient
count. Thus $\varphi(n)<n-1$. Since $\psi(n)\geq n+1$ and $k\geq 1$,
we have $y\geq x>r>1$. In the C4 decomposition of the normalized
difference multiplied by $r^2xy>0$, the term
$r(r^3-1)((x-r)+(y-r))$ is strictly positive and the remaining
terms are nonnegative. This gives strict inequality for composite $n$.
The equality classification is a separate formalization.

## ASSUMED-UNVERIFIED

Worldwide literature coverage, priority, and the model families behind the
preregistration remain unverified.
