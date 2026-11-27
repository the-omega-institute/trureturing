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
Conjecture 7. The complete external endpoint and its bounded literature
screen are preregistered in [#30579](https://github.com/the-omega-institute/trureturing/issues/30579).

## Motivation

This is the source's seventh conjecture with its full $n\ge2$, $k\ge1$
range. The endpoint retains the actual arithmetic functions and the source's
powered pair sums; the exponent is not moved inside an individual function
value or pair sum.

## Gap

Part III Theorem 5 treats $k=1$. The Part IV statements
(DOI 10.3390/math14213935) and the public Lean donor
`pro20541/dimitrov-conjectures-lean` at
`95809b59deefd8dfad81e398250aedd7e1aea3b3` leave the full C7 assertion
uncovered in the bounded source comparison supplied in #30579.

## Route

For $n\ge2$, set $q=(n+1)/n$.
Totient positivity and the public `DimitrovLowerBoundsC4C5.psi_ge` and
`sigma_ge_psi` give $0<x\le y$.
The first projection of `DimitrovPsiSigmaSeparation.separation` gives
$q\le z/y$, so $qy\le z$. Power monotonicity gives
$q^ky^k\le z^k$ and $0<x^k\le y^k\le z^k$, using $q\ge1$.
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

The complete Lean statement is
`D5/S3/Arith/Divisors/DimitrovPairSumC7.claim`, and
`DimitrovPairSumC7.result` carries the saved proof for that statement.
The mirrored source registration is `Reg/D5/S3/Arith/Divisors/DimitrovPairSumC7.lean`
and uses the actual Euler-totient family, with continuation unknown.

The endpoint has the bind-only proof shape and candidate admission basis
`open-problem-resolution (#30579)`. Its Scribe source carries the candidate annotation
`OpenProblemResolutionClaim(dimitrov-2606-12484-conjecture-7, Proved)`.

## Triage

The proof and registration are local candidate sources.
Raw-v3 Scribe consumer compatibility and external qualification remain pending.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources and repository states named
in #30579. Exhaustive coverage and global priority are unverified.
