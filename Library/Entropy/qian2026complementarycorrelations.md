---
bibkey: qian2026complementarycorrelations
authors: Lilong Qian
year: 2026
title: "Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them"
url: https://arxiv.org/abs/2608.14806v2
doi: null
claim: "Lemma 7.1 identifies the complementary-correlation second variation with the quantum Kubo–Mori quadratic form minus the two measured Fisher forms. Definition 7.2 and §11(1) ask whether this difference is nonnegative at every faithful qubit–qutrit product anchor. Section 11(3) asks for a rigorous upper bound on the dimension-five two-ray discrimination score in Eq. (9)."
strata_touched:
  - D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement
  - D5/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity
  - D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold
license: citation-only
triage: anchor
---

# Qian on complementary quantum correlations

## Verified locator

Lilong Qian, arXiv:2608.14806v2 [quant-ph], revision of 19 August 2026.
Lemma 7.1 and equations (38)–(39) identify the second variation at a
faithful product state along a Hermitian direction whose two partial
traces vanish. Definition 7.2 names the nonnegativity of this quadratic
form anchor convexity. Section 11(1) asks for the qubit–qutrit case
and separately asks for the full qubit–qutrit inequality. Proposition
7.6 proves nonnegativity when either marginal is diagonal in either
of its two measured bases, including a maximally mixed marginal.

Section 11(4) asks for a sharp two-ray discrimination constant. The
candidate *Sharp qutrit discrimination and unavoidable correlation
overcounting for complementary measurements*, version 0.1.0-candidate,
published an exact rational sum-of-squares certificate for the sharp bound S ≤ 8/3 on
4 November 2026 (DOI 10.5281/zenodo.23933731). Its correlation section
records counterexamples in covered higher dimensions and leaves the
global qubit–qutrit inequality undecided. The deposit also records
the remaining dimension-five question.

James Schneeloch, Curtis J. Broadbent and John C. Howell,
*Uncertainty relation for mutual information*, Phys. Rev. A 90,
062119 (2014), arXiv:1404.6496, §III, equations (4)–(5), prove the full
inequality when either marginal is diagonal in a measured basis.
This includes a maximally mixed marginal.

- [Qian v2 record](https://arxiv.org/abs/2608.14806v2)
- [Qian v2, §§7 and 11](https://arxiv.org/html/2608.14806v2#S7)
- [Definition 7.2](https://arxiv.org/html/2608.14806v2#S7.Thmtheorem2)
- [Open problem §11(1)](https://arxiv.org/html/2608.14806v2#S11.I1.i1)
- [Schneeloch, Broadbent and Howell](https://arxiv.org/abs/1404.6496)
- [Qutrit discrimination release](https://doi.org/10.5281/zenodo.23933731)

## The five-dimensional threshold

The two-ray family in Eq. (8) uses the score in Eq. (9). Section 11(3) asks for an upper bound at the entropy threshold for orthonormal pairs. Theorem 6.14
gives an exact orthonormal witness attaining the lower endpoint.

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

- [Two-ray family in Eq. (8)](https://arxiv.org/html/2608.14806v2#S6.E8)
- [Score in Eq. (9)](https://arxiv.org/html/2608.14806v2#S6.E9)
- [Theorem 6.14](https://arxiv.org/html/2608.14806v2#S6.Thmtheorem14)
- [Open problem §11(3)](https://arxiv.org/html/2608.14806v2#S11.I1.i3)
