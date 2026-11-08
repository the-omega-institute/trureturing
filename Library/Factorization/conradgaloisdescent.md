---
bibkey: conradgaloisdescent
authors: Keith Conrad
year: 2025
title: "Galois Descent"
doi: null
url: https://www.math.uconn.edu/~kconrad/blurbs/galoistheory/galoisdescent.pdf
claim: "The classical Galois skew algebra acts canonically on the field; Artin independence and the Galois degree identify it with the full endomorphism algebra over the fixed field."
strata_touched:
  - D5/S3/Factorization/Galois/GaloisSkewGroupAlgebra
license: citation-only
triage: anchor
---

# The classical Galois skew algebra

## Verified locator

Source: https://www.math.uconn.edu/~kconrad/blurbs/galoistheory/galoisdescent.pdf

Keith Conrad, *Galois Descent*, Section 2, printed pages 4 and 8–9.
The title page is undated. The bibliographic year above identifies the PDF
build recorded by its metadata, 2025-03-03, rather than a claimed original
publication date. The PDF SHA-256 is
`d50f0a71b61e61dea4d1a31e194e7b50cab7d35239ec1594338aa4c818a617b0`.

## Mathematical correspondence

On page 8, equation (2.8) defines the algebra with basis indexed by the
Galois group, with relations $e_1=1$, $e_\sigma c=\sigma(c)e_\sigma$ and
$e_\sigma e_\tau=e_{\sigma\tau}$. On page 9 the canonical action on the
field is $(\sum_\sigma a_\sigma e_\sigma)(x)=\sum_\sigma a_\sigma\sigma(x)$.
These are the multiplication and action used by `SkewMonoidAlgebra` and
`skewAction`, respectively. Lemma 2.12 on page 4 gives the independence
of distinct characters, including the field automorphisms restricted to
the multiplicative group of the field.

For a finite Galois extension of degree $n$, independence makes this action
injective. Both the skew algebra and the endomorphism algebra over the
fixed field have dimension $n^2$, so the action is an algebra equivalence.
This is the classical finite-dimensional consequence formalized in
`GaloisSkewGroupAlgebra`; the PDF does not label that equivalence as a
separate theorem. The formal statement permits any finite acting group
satisfying `IsGaloisGroup`, using its supplied faithful action and fixed
base field, rather than requiring the group to be literally `Gal(L/K)`.

This citation supports the classical provenance of the construction.
It asserts no literature novelty and no matrix-block or semilinear-descent
conclusion beyond the field skew-algebra equivalence. No source proof body
is vendored.
