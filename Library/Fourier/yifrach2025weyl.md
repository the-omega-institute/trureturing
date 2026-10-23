---
bibkey: yifrach2025weyl
authors: Yuval Yifrach
year: 2025
title: "A note on Weyl's equidistribution theorem"
doi: 10.1007/s00605-025-02057-2
url: https://doi.org/10.1007/s00605-025-02057-2
claim: "Theorem 1.2 gives equidistribution of a real multivariate polynomial with an irrational nonconstant coefficient, using the Euclidean-ball counting measures of Definition 1.1."
strata_touched:
  - D5/S1/Phase/MultivariateWeylRectangles
license: citation-only
triage: anchor
---

# Polynomial equidistribution and the averaging domain

Yifrach, *Monatshefte fuer Mathematik* 206(3), 771–780, Theorem 1.2
on page 772, proves equidistribution modulo one for a real polynomial on
integer lattice points whenever one nonconstant coefficient is irrational.
Definition 1.1 on pages 771–772 defines the averages by counting lattice
points inside Euclidean balls. The publisher PDF and DOI metadata agree
on the author, title, volume, issue, pages and DOI.

For the polynomial alpha times Q, where alpha is irrational and Q is a
nonconstant integer polynomial, every nonzero nonconstant coefficient is
irrational. This places the scalar phase in the scope of Theorem 1.2.
Its ball-shaped averaging domain does not, by itself, yield convergence
on all independently growing rectangles.

The Lean module proves that rectangular statement by coordinate
translation, whole-box smoothing and induction on total degree. All
translations use a coordinate whose derivative of the highest homogeneous
part is nonzero. Each nontrivial difference has degree exactly one less.
For a fixed finite smoothing length the lower-degree correlation limits
hold at a common coordinatewise threshold, and the translation boundary
error tends to zero with the selected side length.

Distinct nonconstant monomials give nonconstant integer combinations for
every nonzero torus character. Fourier density then supplies continuous
observables and fixed nonnegative shifts. Base-B encoding gives distinct
positive degrees along the common curve with coordinates t to the powers
B^i, and positive Haar integrals of continuous functions supported in an
open set give visits in every tail. These are derivations in the module;
this note does not attribute the unrestricted rectangular statement,
its fixed-shift formulation, or its precise curve to Theorem 1.2, and
makes no mathematical novelty claim.

## Verified locator

DOI and publisher article: https://doi.org/10.1007/s00605-025-02057-2
