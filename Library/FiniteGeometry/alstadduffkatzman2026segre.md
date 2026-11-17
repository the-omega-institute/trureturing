---
bibkey: alstadduffkatzman2026segre
authors: Colin Alstad, Timothy Duff, Mordechai Katzman
year: 2026
title: Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras
doi: 10.48550/arXiv.2606.31965
url: https://arxiv.org/abs/2606.31965v1
claim: "Example 4.6 asks whether the eight-point constraints and Segre-determinantal minors give set-theoretic equations for the closed image of two varying pinhole cameras for every n > 8."
strata_touched:
  - D5/S3/Geometry/FlatlandImageAlgebra
  - D5/S3/Geometry/FlatlandImageClosure
  - D5/S3/Geometry/FlatlandImageEquations
license: citation-only
triage: anchor
---

# Two-camera closed-image equations

## Verified locator

DOI: 10.48550/arXiv.2606.31965

Source: https://arxiv.org/abs/2606.31965v1

## Source statements

Example 4.6, page 15, after Equation (38):

> A natural question arises: for $n>8,$ do the $8$-point constraints in Equation (38) and the Segre-determinantal minors suffice to give equations for $\overline{\operatorname{Im}\Theta_{3,(2,2),n}}$?

> To make this more concrete, we may pose the problem of finding the following descriptions of the ideal of the image variety, in increasing order of difficulty: local equations, set-theoretic equations, scheme-theoretic equations, generators of the vanishing ideal, and/or (universal) Gröbner bases.

Definition 4.1, page 12:

> For any $n$, $N$, and $m_\bullet$ as above, we define the associated *image variety* (c.f. [2]) to be the closed image of the rational map

$$
\Theta_{N,m_\bullet,n}:
(\mathbb P^N)^{\times n}\times\mathbb P^{m_\bullet\times N}
\dashrightarrow(\mathbb P^{m_\bullet})^{\times n},
\qquad
(q_\bullet,A_\bullet)\mapsto
\bigl((A_1q_j,\ldots,A_rq_j)\mid 1\le j\le n\bigr).
$$

## Encoding and scope

The complex field, two projective image planes and projective world space of dimension three are retained. Both projective camera matrices vary. The source domain removes every zero camera image. All tuples, including epipoles and rank-one bilinear constraints, remain quantified. Closed image means multihomogeneous polynomial vanishing on the actual rational image.

The Segre column indexed by $(a,b)$ is $x_a y_b$. Signed eight-row maximal cofactors are reshaped with entry $(b,a)$, so $y^TFx=(x\otimes y)^Tc$. Ordered injections enumerate the nine-row minors and eight-row cofactor determinants. Zero cofactors at smaller rank stay in the equations.

The set-theoretic equality concerns the common zero locus. Scheme-theoretic equality, radicality, ideal generators and Gröbner bases require further arguments.
