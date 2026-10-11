---
bibkey: xi2026densitysieve
authors: Ping Xi
year: 2026
title: Horizontal moments of Kloosterman sums and a density version of sieves
doi: null
url: https://arxiv.org/abs/2610.11083v1
claim: Theorem 2.1 transports upper and lower sieve weights to products of local densities. Applied to the actual prime-power correction factors of sigma(N)/N, it preserves the exponent inventory but does not supply a Robin sign or a signed Möbius estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Density sieves and actual Robin prime-power factors

The inspected primary version is [arXiv:2610.11083v1](https://arxiv.org/pdf/2610.11083v1),
submitted 8 October 2026. Its 19-page PDF has SHA-256
`fc77800eb019e6d2da4636b2da9de5e667a110af801416056519346517262759`.
The abstract, Theorems 1.1–1.2, and Theorem 2.1 with its proof on
printed pages 4–5 were inspected. The full moment proofs have not been
independently audited or Lean-verified. No source text is vendored.

## The directly applicable density theorem

Let $\mathcal P$ be a finite prime set and $\Pi=\prod_{p\in\mathcal P}p$.
For local numbers $0\le\delta_p\le1$, Theorem 2.1 states

$$
\sum_{d\mid\Pi}\lambda_d^-\prod_{p\mid d}(1-\delta_p)
\le\prod_{p\in\mathcal P}\delta_p
\le\sum_{d\mid\Pi}\lambda_d^+\prod_{p\mid d}(1-\delta_p),
$$

where $\lambda^-$ and $\lambda^+$ are lower and upper sieve weights.
The relevant sieve condition is

$$
\sum_{d\mid m}\lambda_d^-
\le\mathbf1_{m=1}
\le\sum_{d\mid m}\lambda_d^+
\qquad(m\mid\Pi).
$$

The source proves the statement using auxiliary independent Bernoulli
variables and also announces a deterministic proof in its appendix.
Auxiliary independence does not assert independence of the actual
prime factors of an integer. This theorem is cited as published input;
neither its formulation nor its proof is a new FIB result.

## Parameter correspondence for one actual FIB integer

Fix $N>1$, including an actual $N=1+F_rg$ in the project's canonical
window. Set $a_p=v_p(N)$ for $p\mid N$, take $\mathcal P$ to be exactly
these primes, and put

$$
\delta_{p,N}=1-p^{-a_p-1},\qquad
r_N(d)=\prod_{p\mid d}p^{-a_p-1}\quad(d\mid\operatorname{rad}(N)).
$$

All $a_p\ge1$, so $0<\delta_{p,N}<1$. The classical finite
prime-power geometric sum gives the existing identity

$$
Z(N)=\frac{\sigma(N)}N
=\frac{N}{\varphi(N)}\prod_{p\mid N}\delta_{p,N}.
$$

Directly applying the source theorem therefore gives

$$
\frac{N}{\varphi(N)}\sum_{d\mid\operatorname{rad}(N)}\lambda_d^-r_N(d)
\le Z(N)\le
\frac{N}{\varphi(N)}\sum_{d\mid\operatorname{rad}(N)}\lambda_d^+r_N(d).
$$

This is an application of an existing theorem and Euler-factor identity,
not a new arithmetic estimate. Weights of level $D$ retain only $d\le D$,
but their upper/lower sieve property must still hold on every actual
divisor of the full radical. The local factor uses the exponent in the
same $N$, rather than a separately optimized prime-power inventory.

Theorem 2.1 also permits the local choice
$\delta_{p,N,s}=(1-p^{-a_p-1})^s$ for every real $s>0$.
Thus the same upper and lower sums bound $Z(N)^s$ with prefactor
$(N/\varphi(N))^s$ and divisor weight
$\prod_{p\mid d}[1-(1-p^{-a_p-1})^s]$.
There is no fixed-moment restriction in this finite density identity,
even when $s$ depends on $N$. Averaging it over $N=1+F_rg$ still requires
the joint distribution of these actual valuations and the prefactor;
it does not turn the weight into a fixed multiplicative function of $d$.

To deduce strict Robin for this integer, the upper expression still
needs to be strictly less than $e^\gamma\log\log N$. The density theorem
does not control the factor $N/\varphi(N)$, provide a useful level or
remainder uniformly over the FIB family, or impose the required
same-integer product-window and congruence conditions. Its nonnegative
density interpretation also does not replace the actual signed
$\mu*\beta$ input or the complete $M_zJ_x^{\eta_z}$ pairing.

## Why the horizontal moment theorem is a different input

Theorem 1.1 gives
$\sum_{n\le X}|\mathrm{Kl}(1,n)|\asymp X(\log X)^{8/(3\pi)-1}$.
Theorem 1.2 treats fixed positive moment order $\nu$, weights
$f\in\{1,\mu^2\}$, and specified frequency parameters, on average over
moduli. These absolute moments are not signed cancellation at one
Fibonacci modulus, and their coefficient class does not include the
moving Robin increment weights $b_s$ by direct substitution.
Neither theorem supplies the missing full same-source Robin estimate.
