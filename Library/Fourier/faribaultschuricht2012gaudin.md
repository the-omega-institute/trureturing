---
bibkey: faribaultschuricht2012gaudin
authors: Alexandre Faribault, Dirk Schuricht
year: 2012
title: "On the determinant representations of Gaudin models’ scalar products and form factors"
doi: 10.1088/1751-8113/45/48/485202
url: https://arxiv.org/abs/1207.2352v2
claim: "A Cauchy permanent can be expressed as a determinant with Gaudin-type entries."
strata_touched:
  - D5/S3/Combinatorics/Permanental/CycleGeodesic
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1751-8113/45/48/485202

Source: https://arxiv.org/abs/1207.2352v2

## Identity and conventions

Journal of Physics A: Mathematical and Theoretical 45, article 485202, Section 3. The permanent of the reciprocal-difference matrix $C_{ij}=1/(x_i-y_j)$ equals $\det G$, where

$$G_{ii}=\sum_j\frac1{x_i-y_j}-\sum_{k\ne i}\frac1{x_i-x_k},\qquad
G_{ij}=-\frac1{x_i-x_j}\quad(i\ne j).$$

The row parameters $x_i$ must be distinct and avoid every $y_j$; the column parameters may repeat. Reversing all reciprocal-difference signs changes both sides by $(-1)^n$. This specifies the sign conversion from the paper's Gaudin convention.

The formal proof differentiates Lagrange interpolation to build a nonzero kernel vector for a rectangular Gaudin matrix. A determinant polynomial consequently loses its leading coefficient, and interpolation and induction recover the permanent's column expansion.
