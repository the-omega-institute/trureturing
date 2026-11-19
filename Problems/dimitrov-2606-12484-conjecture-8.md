---
slug: dimitrov-2606-12484-conjecture-8
bibkey: dimitrov2026c8
doi: null
url: https://arxiv.org/abs/2606.12484v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovNesbittC8.result
---

# Dimitrov's Conjecture 8

## Problem

S. I. Dimitrov, *Lower bounds on expressions depending on the functions
φ(n), ψ(n) and σ(n), III*, arXiv:2606.12484v1, §2, PDF page 5,
[Conjecture 8](https://arxiv.org/html/2606.12484v1#Thmconjecture8), states:
“For every integers $k\geq1$ and $n\geq2$, we have”

$$
\begin{aligned}
&\frac{\varphi(n)^k(\psi(n)+\sigma(n))}
{\psi(n)^k(\varphi(n)+\sigma(n))+\sigma(n)^k(\varphi(n)+\psi(n))}
+\frac{\psi(n)^k(\varphi(n)+\sigma(n))}
{\varphi(n)^k(\psi(n)+\sigma(n))+\sigma(n)^k(\varphi(n)+\psi(n))}\\
&+\frac{\sigma(n)^k(\varphi(n)+\psi(n))}
{\varphi(n)^k(\psi(n)+\sigma(n))+\psi(n)^k(\varphi(n)+\sigma(n))}\\
&\geq\frac{n(n+1)^{k-1}(n-1)^k+(n-1)^{2k}+4n^2(n+1)^{2k-2}}
{2n^2(n+1)^{2k-2}+2n(n+1)^{k-1}(n-1)^k}.
\end{aligned}
$$

Here $\varphi$ is Euler's totient,
$\psi(n)=\prod_{p^e\parallel n}p^{e-1}(p+1)$ is Dedekind's function,
and $\sigma(n)=\sum_{d\mid n}d$ is the sum of positive divisors. Function-value
powers are pointwise; all inner mixed sums are unpowered. The original
registration is [#30459](https://github.com/the-omega-institute/trureturing/issues/30459).

## Motivation

`D5/S3/Arith/Divisors/DimitrovNesbittC8.claim` preserves the complete source
statement, and `result` proves it. The native arithmetic functions are
`Nat.totient`, `OeisA344695GcdSigmaPsiPrimes.psi` and `ArithmeticFunction.sigma 1`.
The exponent range includes the original Theorem 6 case $k=1$ and extends to
all $k\ge1$ without a primality or auxiliary-ratio assumption.

## Gap

The original paper labels this exact full statement Conjecture 8. The bounded
source qualification in #30459 checked the original v1, the pinned public Lean
supplier, related Sándor–Gryszka results, and Dimitrov–Lazarova Part 4,
DOI `10.3390/math14213935`, including its original MathML. No explicit full C8
settlement was found in that checked scope. This is no worldwide absence or
priority claim. The Part 4 cube/product and $3k$ formulas have different inner
power conventions and do not themselves state this endpoint.

## Route

Put $u=(n-1)^k$, $d=n(n+1)^{k-1}$ and $R=d/u$. The original arithmetic bounds
and `DimitrovLowerBoundsC4C5.mixed_bound` give $0<A\le B\le C$ and
$1\le R\le B/A\le C/A$. The consumed normalized Nesbitt supplier yields

$$
\frac{4R^2+R+1}{2(R^2+R)}\le
\frac1{B/A+C/A}+\frac{B/A}{1+C/A}+\frac{C/A}{1+B/A}.
$$

The right side is the source left side; the left side is
$(u^2+ud+4d^2)/(2d^2+2ud)$. All denominator positivity follows from
$n\ge2,k\ge1$. Exact normalization reconciles $2k-2=2(k-1)$.

## Falsifier

An exact pair $n\ge2,k\ge1$ violating the original displayed inequality would
refute it. A failure of a stronger supplier condition would not refute it;
finite passing checks, prime-only cases and $k=1$ alone do not settle it.

## Evidence

The proof source is `D5/S3/Arith/Divisors/DimitrovNesbittC8.lean`, with the
paired typed Blueprint Scribe. The source note identifies the consumed
Apache-2.0 supplier, exact revision, file hash, complete license and receiver-pin
retirement condition.

## Triage

### What the settlement shows

**Proved** (`DimitrovNesbittC8.result`): the decisive condition is the common
lower bound on both normalized mixed ratios, supplied by the existing
mixed-power estimate. The analytic port balances the two positive variables
and uses monotonicity of the one-variable lower envelope. The full arithmetic
statement follows with no additional assumptions.

**Proved** (the consumed normalized supplier in the proof of `result`): the
analytic argument needs only $1\le R\le B/A,C/A$. The number-theoretic
interpretation enters through the original arithmetic bridge; the analytic
supplier is prior work, not a new external problem resolution.

**Open**: equality classification over the full arithmetic domain, Conjecture 6,
and the separate Part 4 conjectures. None is asserted settled or counted by this
endpoint. No earlier C4/C5 resolution is repeated here.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the original arXiv v1, the pinned public
Lean supplier, related Sándor–Gryszka results, Dimitrov–Lazarova Part 4, and the
repository searches recorded in #30459. It does not establish exhaustive absence
of another settlement or publication priority. The equality classification and
the neighbouring conjectures listed above remain open.
