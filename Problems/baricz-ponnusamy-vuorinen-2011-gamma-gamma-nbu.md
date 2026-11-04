---
slug: baricz-ponnusamy-vuorinen-2011-gamma-gamma-nbu
bibkey: bariczponnusamyvuorinen2011functional
doi: 10.1016/j.exmath.2011.07.001
triage: theorem
motivation_gids:
  - D5/S3/Analytic/GammaGammaNBU/Result.result
url: https://arxiv.org/abs/1009.4814v2
---

# A counterexample to the gamma-gamma NBU assertion

## Problem

Á. Baricz, S. Ponnusamy and M. Vuorinen, *Functional inequalities for
modified Bessel functions*, Expo. Math. 29(4) (2011), 399–414,
DOI 10.1016/j.exmath.2011.07.001, arXiv:1009.4814v2,
Question 8, printed p. 13:

> Question 8. Is it true that the gamma-gamma distribution satisfies the NBU property?

The preceding definition, printed p. 13, reads:

> By definition a life distribution satisfies the new-is-better-than-used (NBU) property if u ↦ log F̄(u) is sub-additive, i.e.
>
> $$\overline F(u_1+u_2)\le\overline F(u_1)\overline F(u_2)$$
>
> for all u₁, u₂ > 0.

The density, §4, printed p. 10, is introduced as follows:

> The probability density function fₐ,ᵦ,α : (0, ∞) → (0, ∞) of the three parameter gamma-gamma random variable is defined by (see [21])
>
> $$f_{a,b,\alpha}(u)=\frac{2(ab)^{(a+b)/2}u^{(a+b)/2-1}}{\Gamma(a)\Gamma(b)\alpha^{(a+b)/2}}K_{a-b}\!\left(2\sqrt{\frac{ab}{\alpha}u}\right),$$
>
> where a, b > 0 are the distribution shaping parameters, Kν stands for the modified Bessel function of the second kind, and α > 0 is the mean of the gamma-gamma random variable.

### Formal reading

Lean names have prefix `D5.S3.Analytic.GammaGammaNBU.Result`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Modified Bessel function of the second kind | `besselK` | DLMF 10.32.9: $\int_0^\infty e^{-z\cosh t}\cosh(\nu t)\,dt$, for real $\nu$ and $z>0$. |
| Source density | `density` | The displayed density with `Real.Gamma`, real powers and nonnegative square root. |
| Survival function | `survival` | The Lebesgue integral of the density over $(u,\infty)$. |
| Universal NBU assertion | `claim` | Every $a,b,\alpha>0$ and every $u_1,u_2>0$. |
| Refutation | `result` | Exactly $\neg\mathrm{claim}$. |

Only positive arguments occur in the counterexample. The total real
functions outside the source domains impose no additional hypotheses
and do not change the universally quantified positive-domain assertion.

## Motivation

The settling declaration is `D5/S3/Analytic/GammaGammaNBU/Result.result`.
The source notes are `D5/L/Asymptotics/bariczponnusamyvuorinen2011functional`
and `D5/L/Asymptotics/nist2026dlmfbesselkintegral`.
A product of two exponential random variables is already a gamma-gamma
law, and supplies a counterexample to the universal reliability assertion.

## Gap

The universal assertion is false at $a=b=\alpha=1$,
$u_1=u_2=1/2$. At these parameters the source density is
$2K_0(2\sqrt u)$ and the survival function is

$$S(u)=\int_0^\infty e^{-s-u/s}\,ds\quad(u>0).$$

The counterexample concerns Question 8's universal positive parameter
range. It gives no sufficient condition for NBU in other parameter ranges.

## Route

Writing $s=\sqrt t\,e^v$ in the whole-line hyperbolic integral gives

$$2K_0(2\sqrt t)=\int_0^\infty s^{-1}e^{-s-t/s}\,ds.$$

The integrand is nonnegative. Its integral in $t>u$ is $e^{-s-u/s}$,
which is bounded by $e^{-s}$ for $u,s>0$. This proves the product
integrability needed for Fubini and yields the displayed survival identity.

The function $s\mapsto e^{-s-u/s}$ increases up to $\sqrt u$ and decreases
afterwards. Lower sums use 200 cells of width $1/25$ on $[0,8]$; upper
sums use 96 cells of width $1/12$. The upper cell containing $\sqrt{1/2}$
is bounded by $1/4$, since $s+(1/2)/s\ge7/5$ and $e^{-7/5}<1/4$.
Each exponential bound follows from a six-term Taylor enclosure at
$-y/32$, raised to the 32nd power. The tail is at most $e^{-8}<1/1000$.
Consequently,

$$S(1)\ge0.2731>0.2186\ge(0.467)^2\ge S(1/2)^2.$$

## Falsifier

The single positive parameter choice above violates the NBU inequality.
An error in the source density, hyperbolic integral substitution, Fubini
integrability or the directions of the finite-sum bounds would invalidate
the formal refutation.

## Evidence

**PROVED.** `D5.S3.Analytic.GammaGammaNBU.Result.result` states $\neg\mathrm{claim}$.
The theorem uses the exact density and survival definitions above.

The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/7156ef78bc18146678361a7a461b4f9351e79c5a/experiments/baricz-ponnusamy-vuorinen-gamma-gamma-nbu)
contains the following independent numerical checks.

- **COMPUTED.** `python3 gg-cert.py`, exit 0; SHA-256
  `0decfbf57b0ba234cffabbaf925a551a2f224080d0533407a05c650287e3059d`.
  The script checks its $e^{-1}$ enclosure against the alternating Taylor
  sums $S_{23}\le e^{-1}\le S_{22}$.
  Outward-rounded rational quadrature at $a=b=\alpha=1$ gives
  $S(1)\in[0.273125\ldots,0.303005\ldots]$ and
  $S(1/2)\in[0.432959\ldots,0.467563\ldots]$ and verifies the strict
  reverse NBU inequality by exact rational comparison. These displayed
  decimals abbreviate the rational endpoints.
- **COMPUTED.** `python3 gg-scan.py`, exit 0; SHA-256
  `a80cf34185f9b0d087de7300f0196f80392738c4f60c16fbcb0e154e4a6212c7`;
  mpmath precision 30 decimal digits. At $a=b=\alpha=1$ the total mass
  prints as 1.0. Direct density integration and the Bessel closed form
  both give $S(1/2)\approx0.444342523632236041339078102861$.
  For $u\in\{0.01,0.1,0.5,1,2,5\}$ the printed values of
  $S(2u)-S(u)^2$ are respectively
  $0.011396,0.0596991,0.0822915,0.0614176,0.030427,0.00490077$.

The supplied literature check found no settlement of Question 8 in the
searched citations, Formal Conjectures or conjectures.io. The supplied
check of Salazar, arXiv:2607.05538, concerns Questions 1, 2 and 7,
and does not settle Question 8. This bounded scope establishes neither
exhaustive coverage nor priority.

## Triage

### What the settlement shows

NBU implies NBUE, and NBUE implies
$\mathbb E[X^2]\le2\mathbb E[X]^2$ when the moments are finite.
These are standard reliability implications; see Barlow and Proschan,
*Statistical Theory of Reliability and Life Testing: Probability Models* (Holt, Rinehart and Winston, 1975),
for the NBU and NBUE classes. Their mechanism can also be seen directly.
Put $\mu=\int_0^\infty S(x)\,dx=\mathbb E[X]$.
Integration of $S(t+x)\le S(t)S(x)$ in $x$ gives
$\int_t^\infty S(y)\,dy\le\mu S(t)$, the NBUE tail inequality.
Integration in $t$, with Tonelli, gives
$\mathbb E[X^2]/2=\int_0^\infty yS(y)\,dy\le\mu^2$.

The product-gamma construction in the source's §4, with the ordinary
Gamma moment recurrence, gives
$\mathbb E[X]=\alpha$ and
$\mathbb E[X^2]/\mathbb E[X]^2=(1+1/a)(1+1/b)$.
Indeed, independent unit-mean Gamma variables of shapes $a,b$ have
second moments $1+1/a,1+1/b$, and multiplication and scaling by
$\alpha$ give the formula. The source cites P. S. Bithas, N. C. Sagias, P. T. Mathiopoulos,
G. K. Karagiannidis and A. A. Rontogiannis, “On the performance analysis
of digital communications over generalized-K fading channels,”
IEEE Communications Letters 10 (2006), 353–355, for this construction. Thus NBU fails whenever $(1+1/a)(1+1/b)>2$.
At $a=b=1$ the ratio is $4$, strictly above the NBU threshold $2$.
This consequence is a prose derivation, not a Lean theorem of this module.

- **PROVED.** `D5.S3.Analytic.GammaGammaNBU.Result.result` refutes the
  universal assertion by the single witness $a=b=\alpha=1$.
- **COMPUTED.** The certificate and six-point scan above concern only
  $a=b=\alpha=1$. The scan is not a continuous-parameter classification.
- **OPEN.** The range $(1+1/a)(1+1/b)\le2$ is not classified here.
  Avoiding the second-moment obstruction does not prove NBU.
- **OPEN.** The other questions of the source are not settled by this
  module. Its existing theorems retain their stated parameter hypotheses;
  the proposed universal route through log-concavity cannot establish
  NBU in the second-moment obstruction range.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, priority and citation-index completeness
are unverified. No new network literature search is asserted.
The standard reliability implications and the product-Gamma moment
calculation are given in prose; only the fixed counterexample is proved
by the Lean module. The scan's finite-precision values are numerical
observations, not certified uniform bounds.
