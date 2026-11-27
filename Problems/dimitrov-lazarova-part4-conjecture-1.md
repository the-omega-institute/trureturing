---
slug: dimitrov-lazarova-part4-conjecture-1
bibkey: dimitrovlazarova2026part4c2
doi: 10.3390/math14213935
url: https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/DimitrovPartFourC1.result
---

# Dimitrov and Lazarova Part 4, Conjecture 1

## Problem

Dimitrov and Lazarova state Conjecture 1 in Section 4, page 13. For every
natural $n\geq 2$ and $k\geq 1$, they ask whether

$$
\frac{\varphi(n)^{3k}+\psi(n)^{3k}+\sigma(n)^{3k}}
{\varphi(n)^k\psi(n)^k\sigma(n)^k}
\geq \frac{2(n+1)^{3k}+(n-1)^{3k}}{(n+1)^{2k}(n-1)^k}.
$$

Here $\varphi$ is Euler's totient, $\psi(n)=\prod_{p^e\parallel n}p^{e-1}(p+1)$
is Dedekind's psi function, and $\sigma$ is the sum of positive divisors.
Powers are ordinary powers of the function values. The quotients and $n-1$
are real. The Lean functions are `Nat.totient`, `OeisA344695GcdSigmaPsiPrimes.psi`
and `ArithmeticFunction.sigma 1`. [Publisher source and function correspondence](../Library/ArithUnits/dimitrovlazarova2026part4c2.md#conjecture-1)

## Motivation

The source extends its Theorem 1 from exponent one to every positive
integer exponent, with both prime and composite inputs in scope.

## Gap

The tier-1 preregistration records the complete statement and a bounded
comparison of Parts III–IV, Sándor–Gryszka III, and the pinned Mazur donor.
It found no separate published conclusion for the full C1 statement within
that scope. The public repository already had the general cubic ratio
supplier in the frozen C4 owner, where the lemma was private. The exact C1
endpoint is the specialization of that supplier. The earlier #30588
attempt has its own unresolved terminal. [C1 preregistration](https://github.com/the-omega-institute/trureturing/issues/35004)

## Route

Put $A=\varphi(n)^k$, $B=\psi(n)^k$, $C=\sigma(n)^k$, $U=(n-1)^k$ and
$V=(n+1)^k$. Totient positivity, `Nat.totient_lt`, and the public
`DimitrovLowerBoundsC4C5.psi_ge` and `sigma_ge_psi` give
$0<A\leq U\leq V\leq B\leq C$. Thus $r=V/U$, $x=B/A$, $y=C/A$ satisfy
$1\leq r\leq x\leq y$. The original `DimitrovPartFourC4.cubic_ratio_bound`
uses the identity

$$
\begin{aligned}
r^2(1+x^3+y^3)-(1+2r^3)xy
&=r(r^3-1)((x-r)+(y-r)) + 3r^3((x-r)-(y-r))^2\\
&\quad +(4r^3-1)(x-r)(y-r)+r^2((x-r)^3+(y-r)^3).
\end{aligned}
$$

All four terms are nonnegative on the stated range. The supplier gives
$(1+x^3+y^3)/(xy)\geq(1+2r^3)/r^2$. Exact field normalization recovers
$(A^3+B^3+C^3)/(ABC)\geq(2V^3+U^3)/(V^2U)$, the displayed conjecture.
The imported C4/C5 arithmetic development retains its supplier attribution.
[Supplier and license account](../Library/ArithUnits/dimitrov2026c4c5.md)

## Falsifier

An exact natural pair $n\geq 2$, $k\geq 1$ making the displayed left side
strictly smaller than the right side would refute the conjecture.

## Evidence

`D5/S3/Arith/Divisors/DimitrovPartFourC1.result` proves `claim`. The
definition is consumed by `result`, and the endpoint is bind-only under
direct application and field normalization. Its intended admission basis is
`open-problem-resolution` under #35004. The Scribe attaches a typed
`OpenProblemResolutionClaim` with `ResolutionKind.Proved` to the endpoint.
The utility classification is `none`. The result's axiom closure is
`propext`, `Classical.choice` and `Quot.sound`.

The Reg mirror models the full law with the Euler-totient family as the
selected readout. Its bridge uses the original totient, and replacing the
family by the constant zero violates the altered law at $n=2$, $k=1$.
The actual family differs at inputs $2$ and $3$.

The local compiled binding for `DimitrovPartFourC1.result` is
`declared_validated` against the current source, with a source-equivalence
bridge and an unknown continuation.
[Reg source](../Reg/D5/S3/Arith/Divisors/DimitrovPartFourC1.lean)

The local compiled binding for `DimitrovPartFourC4.result` is also
`declared_validated`. The four-slot audit for
`DimitrovPartFourC4.cubic_ratio_bound` is incomplete because the helper has
no binding. [#35028](https://github.com/the-omega-institute/trureturing/issues/35028)

## Triage

### What the settlement shows

The exact inequality holds on the full source range by
`D5/S3/Arith/Divisors/DimitrovPartFourC1.result`. At $k=1$, the right-hand
side expands to $(3n^3+3n^2+9n+1)/(n^3+n^2-n-1)$, recovering
Section 3, Theorem 1, equation (1).

The analytic bound is sharp at $x=y=r$. Indeed, the last nonnegative term
in the cleared difference vanishes exactly at $x=y=r$, which also makes
the other terms vanish. For prime $n$, the identities
$\varphi(n)=n-1$ and $\psi(n)=\sigma(n)=n+1$ give this equality for every
$k\geq 1$. Conversely, $x=r$ implies $VA=UB$. Since $A\leq U$ and
$V\leq B$, equality in $VA\leq VU\leq UB$ gives $A=U$. The $k$th power
is strictly increasing on positive reals for $k\geq 1$, so
$\varphi(n)=n-1$ and `Nat.totient_eq_iff_prime` gives primality. These
equality and sharpness deductions concern the exhibited factorization.
The Lean endpoint states the inequality. Implications for other source
conjectures remain open.

## ASSUMED-UNVERIFIED

The available DOI-index checks reported zero indexed citations. The
OpenAlex citing-works query returned HTTP 429 and Google Scholar required
verification. Exhaustive literature coverage and publication priority
remain unverified. [Bounded literature screen](https://github.com/the-omega-institute/trureturing/issues/35004)
