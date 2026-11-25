---
bibkey: korzekwaetal2019distinguishing
authors: Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol
year: 2019
title: "Distinguishing classically indistinguishable states and channels"
doi: 10.1088/1751-8121/ab30f7
url: "https://arxiv.org/abs/1812.09083v3"
claim: "The paper defines M-distinguishability regions of the probability simplex (classical versions admitting M perfectly distinguishable quantum states), bounds them by permutohedra, analyses the case d=4, M=3 (edges of the permutohedron belong to the region, relative interiors of faces do not), and conjectures from numerical evidence that the points of the region have a product structure over the four face centres (Eq. (30)); it also studies classically indistinguishable channels. Lemma 5 relates pure-state distinguishability to unistochastic matrices with repeated columns. Lemma 6 reduces the mixed problem to pure witnesses on a saturated cap, and Appendix C.3 applies the prior Haagerup method in dimension four. Conjecture 9, Eq. (31), asks whether every M-distinguishability region is star-shaped about the uniform law."
strata_touched:
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityStarShaped
license: citation-only
triage: anchor
---

# Korzekwa, Czachórski, Puchała and Życzkowski, Distinguishing classically indistinguishable states and channels

K. Korzekwa, S. Czachórski, Z. Puchała and K. Życzkowski, J. Phys. A: Math. Theor. 52, 475303 (2019), DOI 10.1088/1751-8121/ab30f7; arXiv:1812.09083v3. Quotations are from the arXiv v3 TeX source `Distinguishability.tex`; macros are expanded.

The classical version of a state $\rho$ is $\operatorname{diag}\rho$ in the preferred basis (l. 236–241). "A $d$-dimensional probability vector $p$ belongs to $M$-distinguishability region $\mathcal A_d^M$ of the probability simplex $\Delta_d$ if and only if there exist $M$ perfectly distinguishable quantum states with the same classical version $p$" (l. 148). For $d=4$, $M=3$ the bounding permutohedron is the tetrahedron of the face centres $f^i$, with $f^1=\frac13(1,1,1,0)$ and the other $f^i$ its permutations, and the paper states (l. 462–467):

> Moreover, based on numerical evidence, we conjecture that points belonging to $\mathcal A^3_4$ have the following product structure:
> $$a b f^1+a (1-b) f^2+(1-a) b f^3+(1-a) (1-b) f^4,$$
> with $a,b\in[0,1]$.

## Three repeated columns in dimension four

The arXiv v3 PDF, p. 5, Lemma 5 and Eq. (19), identifies pure-state
distinguishability at fixed diagonal p with orthonormal columns of squared
moduli p. Completing the columns gives the repeated-column unistochastic
formulation. For three columns in dimension four, row normalization fixes
the fourth column of squared moduli to 1 − 3p. Proposition 4 on the same
page gives the permutohedron bound for the mixed-state region. Lemma 6
(pp. 5–6) supplies a pure replacement whenever some weight attains the cap
1/M.

Section III.B (p. 6) and Appendix C (pp. 18–20) treat the case of three
states in dimension four. Appendix C.2, Eq. (C37), writes the repeated-column
matrix for a specified line of weights. Appendix C.3 reports using Uffe
Haagerup's procedure to test matrices on the repeated-column slice
numerically. Rajchel, Gąsiorowski and Życzkowski describe that procedure in
Appendix A of arXiv:1804.10715v2.

The closed-simplex classification extends the mixed-to-pure conclusion to
every law in the dimension-four, three-state region and gives membership in
the existing `InRegion` predicate by a guarded scalar cubic. The earlier
product refutation provides a point missed by every labelling of Eq. (30).
The classification determines membership at arbitrary simplex points in both
directions. It includes a zero-weight vertex and excludes a point with all
coordinates strictly between zero and the cap.

Appendix C.2, Eqs. (C36)–(C37), uses the negative side of a type-I central
ray. Bengtsson et al., arXiv:math/0402325v2, §IV and Appendix C, exclude
the ray for −1/9 ≤ t < 0 by L = (1 − 3t)/(1 + t) > 1. At t = 0 the flat
matrix has a Hadamard lift, consistent with the L = 1 endpoint in their
Appendix C.

- Lemmas 5 and 6, §III.B, and Appendix C. [arXiv v3 PDF](https://arxiv.org/pdf/1812.09083v3)

## Conjecture 9 and earlier radial results

In §III.C, Eq. (31), arXiv v3 PDF p. 7, Conjecture 9 asserts that
λp + (1−λ)η belongs to the same region as p for all λ in [0,1],
where η is the uniform law. The theorem
`ThreeDistinguishabilityStarShaped.inRegion_uniform_interpolation`
proves this for d = 4 and M = 3. It applies to the full mixed-state
region, including any feasible law with a zero weight, the uniform law
itself, and both interpolation endpoints. Its proof uses the
closed-simplex equivalence `ThreeDistinguishabilityMixedPurity.inRegion_iff_cubic`.
[Conjecture 9 and Remark 10, arXiv v3 PDF p. 7](https://arxiv.org/pdf/1812.09083v3#page=7)

Proposition 12 on the same page lifts pure-state witnesses from a
coarse-grained law q = Gp to p. Its edge application uses a
coarse-graining to a vertex of the bounding permutohedron, as in
Eq. (35). The interpolation theorem starts with any feasible p and
uses the guarded cubic throughout the segment to the uniform law.
[Proposition 12 and Eq. (35), arXiv v3 PDF p. 7](https://arxiv.org/pdf/1812.09083v3#page=7)

- Bengtsson, Ericsson, Kuś, Tadej and Życzkowski treat the specific type-I
  central line with p(u) = (1−3u,1+u,1+u,1+u)/4. Their phase equations give
  feasibility for 0 ≤ u ≤ 1/3 and exclude −1/9 ≤ u < 0.
  [§IV, Eqs. (35)–(40), and Appendix C, Eqs. (56)–(59) and the lemma](https://arxiv.org/pdf/math/0402325v2#page=19)
- Rajchel, Gąsiorowski and Życzkowski prove unistochasticity on
  permutation-to-flat rays in order four and describe Haagerup’s
  order-four membership procedure. The general order-four
  star-shapedness question is discussed in the last paragraph of §6 (PDF p. 12).
  [§6 and Appendix A, Eqs. (7.1)–(7.5) and the modulus test](https://arxiv.org/pdf/1804.10715v2)
- Rajchel-Mieldzioć, Korzekwa, Puchała and Życzkowski prove star-shapedness
  for bracelet and factorisable matrices in Theorem 14 and for circulant
  order-four unistochastic matrices in Theorem 17.
  [arXiv v1 PDF pp. 7 and 9](https://arxiv.org/pdf/2101.11288v1)
- Salazar et al. discuss the general unistochastic star-shapedness
  conjecture in §4.3 and use the order-four circulant case there.
  [arXiv:2405.05785, PDF p. 26](https://arxiv.org/pdf/2405.05785#page=26)

Completing the weighted isometry identifies the region with the
repeated-column slice T(p) = [p,p,p,1−3p] of order-four unistochastic
matrices. Since T is affine, the interpolation theorem gives segments
from the flat matrix within this slice. Remark 10 relates Conjecture 9
to the separate question for unrestricted unistochastic matrices.
[Remark 10, arXiv v3 PDF p. 7](https://arxiv.org/pdf/1812.09083v3#page=7)

## Verified locator

- DOI: https://doi.org/10.1088/1751-8121/ab30f7
- Source: https://arxiv.org/abs/1812.09083v3
