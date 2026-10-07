---
bibkey: bishnoi2017finitegrid
authors: Anurag Bishnoi, Pete L. Clark, Aditya Potukuchi and John R. Schmitt
year: 2017
title: On zeros of a polynomial in a finite grid
doi: 10.48550/arXiv.1508.06020
url: https://arxiv.org/abs/1508.06020v2
claim: Corollary 6.8 gives the minimum n(q-1)+1 for affine hyperplane blocking sets in AG(n,q); its n=2 case is the all-line minimum 2q-1 over every finite field.
strata_touched:
  - D5/S3/Geometry/FiniteGeometry/AffineBlockingBound
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Geometry/bishnoi2017finitegrid -->
# The affine-plane blocking minimum

Anurag Bishnoi, Pete L. Clark, Aditya Potukuchi and John R. Schmitt,
*On zeros of a polynomial in a finite grid*, arXiv:1508.06020v2,
12 June 2017. Primary text: https://arxiv.org/pdf/1508.06020v2.

Corollary 6.8, PDF page 16, states that a smallest blocking set in AG(n,q)
has n(q-1)+1 points. Section 6.2 defines blocking as meeting every affine
hyperplane over the finite field of order q. There is no prime-order or
odd-characteristic restriction. The paper attributes the result to Jamison
and to Brouwer and Schrijver. In dimension two, affine hyperplanes are lines,
and the minimum is 2q-1.

In the formal statement the plane is the native product F x F, and its lines
are the fibres phi(p)=c of all nonzero F-linear maps phi to F, with every
offset c in F. A nonzero linear functional on this plane has a nonzero
coefficient and is surjective; each fibre is a translate of its
one-dimensional kernel. Thus these fibres describe the affine lines in the
source's n=2 setting, including the zero offset.

The proof chooses b0 in a blocking set B. For b in B other than b0, form
the factor 1-(b.1-b0.1)u-(b.2-b0.2)v, and multiply these factors to obtain P.
At the zero covector P is one. For a nonzero covector (u,v), the native
linear map phi(x,y)=u*x+v*y is nonzero. Blocking at phi(b0)+1 gives a point
b distinct from b0 with phi(b-b0)=1, so a factor vanishes. Consequently P
vanishes at every other covector. Its total degree is at most |B|-1.
Mathlib's finite-field evaluation-sum theorem excludes this singleton
support at degree less than 2(q-1), proving |B| at least 2q-1.

The two coordinate axes meet every fibre of every nonzero functional:
division by a nonzero coefficient gives a point with any prescribed image.
The axes each have q points and share only the origin, attaining 2q-1.

The formal theorem covers the n=2 case only. It does not formalize the full
Alon--Furedi theorem or Corollary 6.8 in arbitrary dimension, nor assert a
result for arbitrary incidence planes, nonfield rings, selected direction
families or projective blocking sets. The singleton-support argument uses
Mathlib's evaluation-sum theorem; the finite-geometry result remains
literature-attested, without an originality claim.

## Verified locator

DOI resolver: https://doi.org/10.48550/arXiv.1508.06020
Declared URL: https://arxiv.org/abs/1508.06020v2
Corollary 6.8, PDF page 16; blocking-set definition in Section 6.2,
PDF pages 15-16.
