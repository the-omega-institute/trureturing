---
bibkey: garrappagerholdpopoliziosimon2025mittagleffler
authors: R. Garrappa, S. Gerhold, M. Popolizio and T. Simon
year: 2025
title: On some inequalities for the two-parameter Mittag-Leffler function in the complex plane
doi: 10.1016/j.jmaa.2025.129588
url: https://arxiv.org/abs/2410.11852
claim: "Remark 6 asks whether the real-axis Kummer value universally bounds the complex modulus from below."
strata_touched:
  - D5/S3/Analytic/KummerModulusLowerBound/Result
license: citation-only
triage: anchor
---

# The Kummer modulus question

## Verified locator

https://arxiv.org/abs/2410.11852

Version: https://arxiv.org/abs/2410.11852v4, Remark 6 and Remark 2(a).
J. Math. Anal. Appl. 551(1) (2025), 129588.
DOI: 10.1016/j.jmaa.2025.129588. arXiv:2410.11852.
The supplied source locator specifies remarks, without a verified page number.

## Source statements

Remark 6:

> In view of the preceding result and Remark 2, one may ask if for all α, β > 0 one has |M(α, α−β, z)| ≥ M(α, α−β, ℜz), z ∈ ℂ. (2.4) … In particular, (2.4) holds globally for α > 1 ≥ β > 0 … The question whether (2.4) holds globally for all α, β > 0 seems to be still open.

Remark 2(a) identifies M as "a Kummer confluent hypergeometric function": M(a, b, z) = Σ_{n≥0} (a)_n z^n / ((b)_n n!), b ∉ {0, −1, −2, …}.

## Mathematical correspondence

The coefficient is the existing `KummerRatio.Defs.kummerCoeff`:
$(a)_n/((b)_n n!)$, with rising factorials evaluated by `ascPochhammer`.
The complex series casts precisely these real coefficients into ℂ.
The real side is the existing `KummerRatio.Defs.kummer`, without a change
of normalization. The nonpole condition excludes $b=0,-1,-2,\ldots$.

At $a=1/2$, $b=-3/2$ the series is
$e^z(1-4z/3+4z^2/3)$. Its value is zero at
$z=1/2+i\sqrt2/2$, whereas its real-axis value there is
$(2/3)e^{1/2}>0$. The answer to the universal question is negative.
The range $\alpha>1\ge\beta>0$ stated in Remark 6 is not contradicted.
The remaining parameter-region question is described in
`Problems/garrappa-gerhold-popolizio-simon-2025-kummer-modulus.md`.
