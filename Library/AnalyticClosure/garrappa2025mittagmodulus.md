---
bibkey: garrappa2025mittagmodulus
authors: Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon
year: 2025
title: On some inequalities for the two-parameter Mittag-Leffler function in the complex plane
doi: null
url: https://arxiv.org/abs/2410.11852v4
claim: "Conjecture 25 characterizes the global reverse modulus inequality by the parameter interval and complete monotonicity of the reciprocal."
strata_touched:
  - D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2410.11852v4

The quoted text is from the fourth arXiv version, pages 1 and 18. The journal
version of record has not been read.

## Source statement

Page 1, equation (1.1):

> In this paper we study several inequalities of the two-parameter Mittag-Leffler function $E_{\alpha,\beta}$, which is defined on the complex plane for $\alpha > 0$ and $\beta\in\mathbb{R}$ by the series representation
> $E_{\alpha,\beta}(z) = \sum_{k=0}^{\infty} \frac{z^k}{\Gamma(\alpha k + \beta )}, \qquad z \in \mathbb{C}.$

Page 18:

> Conjecture 25. For every α ∈ (1, 2), one has
> The inequality (1.4) holds globally ⇐⇒ β ∈ [α − 1, α] ⇐⇒ 1/Eα,β(x) is CM on (0, ∞).

Here (1.4) is $|E_{\alpha,\beta}(z)|\ge E_{\alpha,\beta}(\Re z)$,
and globally means every complex $z$. The paper considers $\beta\ge0$ in this
inequality problem. Its CM definition requires a smooth positive-valued
function on the positive half-line and nonnegative signed derivatives of
every natural order.

## Mathematical scope

The Lean series relation uses `HasSum` for every positive real alpha, arbitrary
real beta and complex argument. Reciprocal Gamma is zero at its poles under
Mathlib's totalized division. The claim includes existence of the whole
series family, both stated equivalences, and the positive codomain in the CM
clause. Real arguments are embedded in the complex plane, with the real part
reading the real-valued series there.

The refutation uses alpha = 3/2, beta = 1/2 and z = −115 + 10i. Sixty-four
terms and an error at most 4/10^13 separate the modulus at this point from
the value at −115. This certifies failure of the interval-to-global-inequality
implication. It does not prove the all-alpha family or an interior-beta
neighbourhood. The paper reports the other forward implications as proved;
those implications are not challenged by this example.

## Independent computation and literature boundary

The separate exact rational checker is in
`the-omega-institute/trureturing-experiments`, commit
`f1be70a8a80297f44ec7a3d651faf1e622920913`, at
`docs/reports/mittag-leffler-modulus-inequality/check.py`.
Its SHA256 is `c6baf5bbab39481e1235752ddd18164291344b7bcfa8a7e11c51fb62a56aa2ff`.
The preregistration reports `python3 check.py`, exit 0, `ALL_CHECKS_OK`, for
the larger witnesses r = 1024, 1536 and 2048 on z = r(−1+i/2).
These computation readings are distinct from the kernel proof at −115+10i.

The literature screen in issue #22376 is partial. Completeness and absence of
an earlier external settlement are ASSUMED-UNVERIFIED. Inaccessible citation
APIs, the unread journal version, and unread full texts prevent an exhaustive
priority claim. No new general Gamma identity or asymptotic expansion is
claimed.
