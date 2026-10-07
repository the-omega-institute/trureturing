---
bibkey: dokmanic2015euclideandistancematrices
authors: Ivan Dokmanić, Reza Parhizkar, Juri Ranieri, Martin Vetterli
year: 2015
title: "Euclidean Distance Matrices: Essential Theory, Algorithms and Applications"
doi: 10.1109/MSP.2015.2398954
url: https://arxiv.org/abs/1502.07541v2
claim: Section II.B, equation (10), reconstructs the anchored Gram matrix from squared Euclidean distances; its positive semidefinite factorization reconstructs a point configuration up to rigid transformations.
strata_touched: []
license: citation-only
triage: anchor
---

# Anchored distance geometry

Ivan Dokmanić, Reza Parhizkar, Juri Ranieri and Martin Vetterli, *Euclidean Distance Matrices: Essential Theory, Algorithms and Applications*, IEEE Signal Processing Magazine 32(6), 12–30. The [primary preprint, arXiv:1502.07541v2](https://arxiv.org/pdf/1502.07541v2), lists all four authors on its first page.

Section II.B, “Reconstructing the Point Set From Distances”, pp. 4–5, fixes the first point at the origin. Its matrix $D$ contains **squared** distances. With $d_1=De_1$, equation (10) is

$$
G=X^{\mathsf T}X=-\frac12\bigl(D-\mathbf1d_1^{\mathsf T}-d_1\mathbf1^{\mathsf T}\bigr).
$$

Thus, for base event $O$, the non-base entries are $G_{ij}=(d(O,x_i)^2+d(O,x_j)^2-d(x_i,x_j)^2)/2$. The ensuing eigenvalue factorization uses nonnegative eigenvalues of $G$ and removes zero rows to obtain the dimension of the anchored span. The preceding equations (5)–(7) explain invariance under orthogonal transformations, including reflections, and translations. Distances do not select an absolute position or an orientation.

The note supplies the classical intermediate reconstruction used in [the observer-internal three-axis volume](../../docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md), §§2–3 and the proof of §10.2. Its use requires one common point configuration and one length calibration. It supplies neither an ordered FIB response, a Jacobi condition, an operational measurement permission, nor identification with the joint-state predictive quotient. That identification in §10.2 is established from the common-source calibration matrix and generator closure, rather than from a shared dimension count.
