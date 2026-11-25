---
bibkey: korzekwaetal2019distinguishing
authors: Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol
year: 2019
title: "Distinguishing classically indistinguishable states and channels"
doi: 10.1088/1751-8121/ab30f7
url: "https://arxiv.org/abs/1812.09083v3"
claim: "The paper defines M-distinguishability regions of the probability simplex (classical versions admitting M perfectly distinguishable quantum states), bounds them by permutohedra, analyses the case d=4, M=3 (edges of the permutohedron belong to the region, relative interiors of faces do not), and conjectures from numerical evidence that the points of the region have a product structure over the four face centres (Eq. (30)); it also studies classically indistinguishable channels. Lemma 5 relates pure-state distinguishability to unistochastic matrices with repeated columns. Lemma 6 reduces the mixed problem to pure witnesses on a saturated cap, and Appendix C.3 applies the prior Haagerup method in dimension four."
strata_touched:
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic
  - D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity
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

## Verified locator

- DOI: https://doi.org/10.1088/1751-8121/ab30f7
- Source: https://arxiv.org/abs/1812.09083v3
