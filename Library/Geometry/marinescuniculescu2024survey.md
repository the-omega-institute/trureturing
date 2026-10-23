---
bibkey: marinescuniculescu2024survey
authors: D.-Ş. Marinescu; C. P. Niculescu
year: 2024
title: "A survey of the Hornich-Hlawka inequality"
doi: null
url: https://arxiv.org/abs/2407.03278v1
claim: "Section 6 derives the scalar multiplicative Hornich–Hlawka inequality from Theorem 8 and states that no extension to inner product spaces is known."
strata_touched:
  - D5/S3/Geometry/MultiplicativeHornichHlawka
  - D5/S3/Geometry/VariableExponentHornichHlawka
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2407.03278v1>.
D.-Ş. Marinescu, C. P. Niculescu, *A survey of the Hornich-Hlawka inequality*, arXiv:2407.03278v1, §6, the paragraph applying Theorem 8 to $f(x)=\ln(1+x)$.
The same survey, §3, Problem 3, asks whether every $L^{p(\cdot)}(0,1)$ space with a variable exponent $p(\cdot):(0,1)\to[1,2]$ is a Hornich–Hlawka space; the Luxemburg norm convention follows the monograph of Diening, Harjulehto, Hästö and Růžička cited there.

## Multiplicative inequality

The paragraph states verbatim:

> Applying Theorem 8 to the function f (x) = ln(1 + x) one obtains the multiplicative analog of the inequality (2.1), (1 + |x|)(1 + |y|)(1 + |z|)(1 + |x + y + z|) ≥ (1 + |x + y|)(1 + |y + z|)(1 + |z + x|), for all x, y, z ∈ R. No extension of this remark to the case of inner product spaces is known.

Theorem 8 uses the derivative signs $f'\ge0$, $f''\le0$, $f'''\ge0$. For $f(t)=\ln(1+t)$ on $[0,\infty)$, the derivatives are $(1+t)^{-1}$, $-(1+t)^{-2}$, and $2(1+t)^{-3}$. The scalar conclusion does not itself supply an inner-product-space extension; the survey's power-function transfer does not apply to this logarithm.

## Related results

Ressel, *Journal of Mathematical Inequalities* **9** (2015), 883–888, proves the Hornich–Hlawka inequality on the real line for Bernstein functions and a Euclidean square-root case. The evidence for this description is the abstract; the full text is ASSUMED-UNVERIFIED.

El Idrissi–Zoubeir, arXiv:2601.18768, prove the Ptolemy-type strengthening

$$
\|x\|\|y\|+\|z\|\|x+y+z\|\ge\|x+z\|\|y+z\|.
$$

## Repository-derived result

The companion Lean theorem proves, for every real or complex inner product space and all $x,y,z$,

$$
(1+\|x+y\|)(1+\|y+z\|)(1+\|z+x\|)
\le (1+\|x\|)(1+\|y\|)(1+\|z\|)(1+\|x+y+z\|).
$$

Ptolemy bounds the second elementary symmetric function of the three pair-sum norms by that of the four remaining norms. The Fréchet identity, together with the Ptolemy comparisons, gives the first comparison. A cubic factorization, together with four triangle inequalities, gives the third comparison. Expanding the products completes the proof. Neither finite dimension nor completeness is required.

## ASSUMED-UNVERIFIED

The journal version of the survey and the full text of Ressel (2015) are unverified. The survey locator and quotation bind to arXiv:2407.03278v1; the Ressel comparison is limited to its abstract. Equality cases and extensions to every Hornich–Hlawka normed space or to every Bernstein function in inner product spaces are not established by this module.
