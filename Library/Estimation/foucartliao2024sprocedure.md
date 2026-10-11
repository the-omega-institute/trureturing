---
bibkey: foucartliao2024sprocedure
authors: Simon Foucart; Chunyang Liao
year: 2024
title: "S-Procedure Relaxation: a Case of Exactness Involving Chebyshev Centers"
doi: 10.1007/978-3-031-66497-7_1
url: https://arxiv.org/abs/2310.09677v1
claim: "Section 5, Question 2 asks whether the Chebyshev center is always obtained via quadratic regularization in the real optimal-recovery setting."
strata_touched:
  - D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization
license: citation-only
triage: anchor
---

## Locator

DOI: [10.1007/978-3-031-66497-7_1](https://doi.org/10.1007/978-3-031-66497-7_1).
Author text: <https://arxiv.org/abs/2310.09677v1>.
Published in *Explorations in the Mathematics of Data Science* (Springer, 2024).
Section 5, “Some Open Questions”, Question 2:

> Is the Chebyshev center always obtained via regularization?

The authors explain:

> From [10], we know that the answer is affirmative under the specific conditions mentioned above, since the Chebyshev center equals the regularizer $f_{\tau_\sharp}$ with parameter $\tau_\sharp\in(0,1)$ satisfying the implicit equation (9). Without the specific conditions, we also know from [8] that the answer is affirmative if one considered the complex setting rather than the real setting.

## Optimal recovery and regularization

Section 5 takes $Q=\mathrm{Id}_H$ and the model and error sets (25)

$$
\mathcal K=\{f\in H:\|Pf\|_H\leq\varepsilon\},\qquad
\mathcal E=\{e\in\mathbb R^m:\|e\|_2\leq\varepsilon\}.
$$

The feasible set at data $y$ consists of the $f$ satisfying both
$\|Pf\|\leq\varepsilon$ and $\|y-\Lambda f\|\leq\varepsilon$.
The specific conditions are that $P$ is an orthogonal projector and
$\Lambda\Lambda^*=\mathrm{Id}_m$. Equation (8) defines

$$
f_\tau=\operatorname{argmin}_f
\bigl((1-\tau)\|Pf\|^2+\tau\|y-\Lambda f\|^2\bigr).
$$

**Repository-derived counterexample.** In $H=\mathbb R^2$, take
$P=\operatorname{diag}(1,0)$,
$\Lambda=\left(\begin{smallmatrix}1/2&-1/2\\0&1\end{smallmatrix}\right)$,
$y=(1,0)$ and both bounds equal to one. The Chebyshev center is
$c_*=(3/5,-1/5)$ with radius $\sqrt{4/5}$. The point
$v=(3/5,-7/25)$ has the same squared model norm $9/25$ and a
strictly smaller squared data residual, $49/125<50/125$.
Consequently $c_*$ minimizes no such objective with $\tau\in(0,1)$.
The theorem
`D5.S3.Analytic.OptimalRecovery.ChebyshevCenterRegularization.result`
proves the negation of the universal real assertion. This example
retains the projector condition and violates the row-isometry condition.

## Related literature and scope

Foucart–Liao, arXiv:2401.11112, concerns the global setting only;
Foucart–Hengartner, arXiv:2406.14418, and Lin–Du, arXiv:2506.00704,
do not answer this local-center question. These references do not
establish an exhaustive priority claim.

**ASSUMED-UNVERIFIED:** classical work on Chebyshev centers of
intersections of two ellipsoids, including Beck–Eldar (2007) and
follow-ups, has not been checked for an earlier real instance whose
center lies on no regularization path.

Citation only; no source PDF or TeX is redistributed.
