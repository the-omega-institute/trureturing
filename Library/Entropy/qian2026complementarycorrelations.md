---
bibkey: qian2026complementarycorrelations
authors: Lilong Qian
year: 2026
title: "Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them"
doi: null
url: https://arxiv.org/abs/2608.14806v2
claim: "Equation (8) gives the two-ray family, and Eq. (9) defines its two-basis triangular-discrimination score. Theorem 6.14 gives exact attainment in dimension five. Section 11(3) asks for an upper bound at the entropy threshold for orthonormal pairs."
strata_touched:
  - D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold
license: citation-only
triage: anchor
---

# Qian on complementary quantum correlations

## Verified locator

Lilong Qian, arXiv:2608.14806v2 [quant-ph], revised 19 August 2026.
Equation (8) gives the two-ray family. Equation (9) adds the triangular
discrimination of the two Born probability tables in the computational
and Fourier bases. Section 11(3) asks for
an upper bound at the entropy threshold for orthonormal pairs in
dimension five. Theorem 6.14 supplies an exact orthonormal witness
with score $(14+2\sqrt{5})/5$. [arXiv record](https://arxiv.org/abs/2608.14806v2)
· [Two-ray family in Eq. (8)](https://arxiv.org/html/2608.14806v2#S6.E8)
· [Score in Eq. (9)](https://arxiv.org/html/2608.14806v2#S6.E9)
· [Theorem 6.14](https://arxiv.org/html/2608.14806v2#S6.Thmtheorem14)
· [§11(3)](https://arxiv.org/html/2608.14806v2#S11.I1.i3)

## The five-dimensional threshold

For unit vectors $x,y\in\mathbb C^5$ the two tables use $|x_i|^2,|y_i|^2$
and $|(Fx)_i|^2,|(Fy)_i|^2$, where $F_{ij}=5^{-1/2}\exp(2\pi\mathrm i\,ij/5)$
and a common zero row contributes zero. Let $D$ be the sum of
$pq/(p+q)$ over both tables. The two laws each have total mass two,
so $S=4-4D$. The Lean theorem proves
$S\le 4-8E+8E^2/A<377/100$, with
$A=1-\sqrt{(5+\sqrt 5)/10}$ and $E=1-\sqrt{(7+\sqrt 5)/10}$.
The exact certificate is
$D\ge 2E-2E^2/A\ge 53682/933125>23/400$.
Simultaneous conjugation gives the same bound in the opposite Fourier
convention. The unit norm hypotheses alone suffice.

Theorem 6.14 and the upper bound give
`(14+2√5)/5 ≤ M₅ ≤ 4−8E+8E²/A < 377/100`
for the orthonormal-pair maximum $M_5$. The same interval holds for the
maximum over all unit pairs. The exact maximum remains open. The
analytic lower endpoint is credited to Qian's witness.

## Prior qutrit certificate

*Sharp qutrit discrimination and unavoidable correlation overcounting for
complementary measurements*, version 0.1.0-candidate, supplies an exact
rational sum-of-squares certificate for the sharp $8/3$ qutrit bound in
§11(4). The deposit records the residual dimension-five question.
[Zenodo DOI 10.5281/zenodo.23933731](https://doi.org/10.5281/zenodo.23933731)
