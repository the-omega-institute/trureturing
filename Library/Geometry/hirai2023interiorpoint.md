---
bibkey: hirai2023interiorpoint
authors: Hiroshi Hirai, Harold Nieuwboer, and Michael Walter
year: 2023
title: "Interior-point methods on manifolds: theory and applications"
doi: 10.48550/arXiv.2303.04771
url: https://arxiv.org/abs/2303.04771
claim: "Lemma 5.13 and Remark 5.14 concern the hyperbolic cotangent inequality and its optimal coefficient; Theorem 5.15 relates this estimate to self-concordance of squared distance on positive definite matrices."
strata_touched:
  - D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant
license: citation-only
triage: anchor
---

# Interior-point methods on manifolds

H. Hirai, H. Nieuwboer, and M. Walter, *Interior-point methods on manifolds:
theory and applications*, arXiv:2303.04771v2.

## Locator

arXiv:2303.04771v2, §5, Lemma 5.13 and Remark 5.14.
Source: https://arxiv.org/abs/2303.04771.

DOI: 10.48550/arXiv.2303.04771.

> "Lemma 5.13. The constant C = √2 is such that for all a, b ∈ ℝ, one has |coth((a − b)/2) (a coth(a/2) − b coth(b/2))| ≤ C √(ab(a − b) coth(a/2) coth(b/2) coth((a − b)/2))."

> "Remark 5.14. We conjecture, based on numerical evidence, that the optimal constant in the above inequality is C = 1/√2."

The source proves the coefficient $\sqrt2$ and conjectures that the optimal
coefficient is $1/\sqrt2$.

For nonzero real $a,b$ with $a\ne b$, the scalar estimate has the form

$$
\left|\coth\frac{a-b}{2}
\left(a\coth\frac a2-b\coth\frac b2\right)\right|
\le C\sqrt{ab(a-b)\coth\frac a2\coth\frac b2\coth\frac{a-b}{2}}.
$$

The repository resolves the source conjecture: the estimate holds uniformly
at $C=1/\sqrt2$, and every smaller real coefficient fails for some
permitted pair. The source definitions and assertion are attributed to the
paper; the analytic proof and its Lean implementation are repository results.

## Geometric consequence

Via the paper's Theorem 5.15, the sharp scalar estimate implies that squared
distance on $\mathrm{PD}(n)$ is $8$-self-concordant. This geometric consequence
is not formalized by the scalar declaration.

The note does not establish bibliographic priority or the absence of a later
proof in the literature.
