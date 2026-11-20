---
bibkey: hopf1931abbildungen
authors: Heinz Hopf
year: 1931
title: "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche"
doi: 10.1007/BF01457962
claim: "The quadratic map of the unit three-sphere of R^4 onto the unit two-sphere of R^3 given in Section 5 has as preimage of every point a great circle of the three-sphere."
strata_touched:
  - D5/S3/Quantum/AURICOmega/QuaternionRayKernel
  - D5/S3/Quantum/AURICOmega/QuaternionHopfFibration
license: citation-only
triage: anchor
---

# Hopf, maps of the three-sphere onto the two-sphere

## Verified locator

- DOI: https://doi.org/10.1007/BF01457962

Mathematische Annalen 104 (1931), no. 1, 637–665. The DOI registration lists
the author Heinz Hopf, this title, volume 104, issue 1, pages 637–665 and
publication in December 1931, and resolves to the publisher page
http://link.springer.com/10.1007/BF01457962. The interior locator below was
read on a scan of the printed article (pages 637–665).

- Section 5, "Eine Abbildung der S^3 auf die S^2 mit γ = 1", pages 654–655,
  formulas (1), (2), (4) and (5).

## Statement

Section 5 maps the Euclidean space with coordinates $x_1, x_2, x_3, x_4$ to the
Euclidean space with coordinates $\xi_1, \xi_2, \xi_3$ by
$\xi_1 = 2(x_1x_3 + x_2x_4)$, $\xi_2 = 2(x_2x_3 - x_1x_4)$,
$\xi_3 = x_1^2 + x_2^2 - x_3^2 - x_4^2$ (formula (1)), and observes
$\xi_1^2 + \xi_2^2 + \xi_3^2 = (x_1^2 + x_2^2 + x_3^2 + x_4^2)^2$ (formula (2)),
so the unit three-sphere is mapped onto the unit two-sphere. On the Riemann
sphere the map is $z = (x_1 + i x_2)/(x_3 + i x_4)$ (formula (4)). The
preimage of every point of the two-sphere is the intersection of the
three-sphere with two distinct hyperplanes through the origin given by the two
linear equations (5), hence a great circle; these great circles form a
Clifford parallel system (footnote 13).

## Encoding and boundary

The repository map is `hopf x = x * i * star x` on unit quaternions. With
$x = a + b\,i + c\,j + d\,k$ and Hopf's coordinates
$(x_1, x_2, x_3, x_4) = (a, b, d, c)$, its $i$, $j$ and $k$ components are
$\xi_3$, $\xi_1$ and $\xi_2$ of formula (1); this identification was checked by
expanding the quaternion product. The great circle through $x$ is described in
the repository as the right coset $x \cdot S$ of the circle $S$ of unit
quaternions in the real span of $1$ and $i$. The ray kernel, its identity with
the inner product of the Hopf images, its characterization of the coset
circles, and the identification with the trace pairing of two rank-one
projections on complex two-space are not stated in the source.

## What this note does and does not attest

Attested here: the bibliographic record and DOI, and the content of Section 5,
pages 654–655, formulas (1), (2), (4), (5) and footnote 13, as quoted above.

Not attested here: any other section of the article; the linking-number
results of the article are not used.
