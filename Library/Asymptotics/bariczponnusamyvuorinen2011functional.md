---
bibkey: bariczponnusamyvuorinen2011functional
authors: Á. Baricz, S. Ponnusamy and M. Vuorinen
year: 2011
title: Functional inequalities for modified Bessel functions
doi: 10.1016/j.exmath.2011.07.001
url: https://arxiv.org/abs/1009.4814v2
claim: "Question 8 asks whether the gamma-gamma distribution has the new-is-better-than-used property."
strata_touched:
  - D5/S3/Analytic/GammaGammaNBU/Result
license: citation-only
triage: anchor
---

# The gamma-gamma NBU question

## Verified locator

https://arxiv.org/abs/1009.4814v2

arXiv:1009.4814v2; Expositiones Mathematicae 29(4) (2011), 399–414;
DOI: 10.1016/j.exmath.2011.07.001.
The locators below use the printed pages of the arXiv version.

## Density

Section 4, printed p. 10:

> The probability density function fₐ,ᵦ,α : (0, ∞) → (0, ∞) of the three parameter gamma-gamma random variable is defined by (see [21])
>
> $$f_{a,b,\alpha}(u)=\frac{2(ab)^{(a+b)/2}u^{(a+b)/2-1}}{\Gamma(a)\Gamma(b)\alpha^{(a+b)/2}}K_{a-b}\!\left(2\sqrt{\frac{ab}{\alpha}u}\right),$$
>
> where a, b > 0 are the distribution shaping parameters, Kν stands for the modified Bessel function of the second kind, and α > 0 is the mean of the gamma-gamma random variable.

## NBU and Question 8

Section 5, printed p. 13:

> By definition a life distribution satisfies the new-is-better-than-used (NBU) property if u ↦ log F̄(u) is sub-additive, i.e.
>
> $$\overline F(u_1+u_2)\le\overline F(u_1)\overline F(u_2)$$
>
> for all u₁, u₂ > 0.

> Question 8. Is it true that the gamma-gamma distribution satisfies the NBU property?

The overbar distinguishes the survival function from the cumulative
distribution function. The survival function is the integral of the
density on $(u,\infty)$. At $a=b=\alpha=1$ the density is
$2K_0(2\sqrt u)$.
