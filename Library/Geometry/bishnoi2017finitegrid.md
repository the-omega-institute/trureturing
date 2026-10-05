---
bibkey: bishnoi2017finitegrid
authors: Anurag Bishnoi, Pete L. Clark, Aditya Potukuchi and John R. Schmitt
year: 2017
title: On zeros of a polynomial in a finite grid
doi: 10.48550/arXiv.1508.06020
url: https://arxiv.org/abs/1508.06020v2
claim: Corollary 6.8 gives the exact minimum n(q-1)+1 for affine hyperplane blocking sets in AG(n,q); in dimension two this is the all-line blocking minimum 2q-1 over every finite field.
strata_touched:
  - D5/S3/Geometry/FiniteGeometry/AffineBlockingBound
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Geometry/bishnoi2017finitegrid -->
# The affine blocking minimum and finite-grid polynomials

Anurag Bishnoi, Pete L. Clark, Aditya Potukuchi and John R. Schmitt,
*On zeros of a polynomial in a finite grid*, arXiv:1508.06020v2,
12 June 2017. The first arXiv submission is from 2015; the cited text is
the second version. Primary text: https://arxiv.org/pdf/1508.06020v2.

Corollary 6.8, manuscript page 16, states that the minimum size of a blocking
set in AG(n,q) is n(q-1)+1. Section 6.2 defines blocking by intersection
with every affine hyperplane. Here q is a finite field order, with no
restriction to prime q or odd characteristic. For n=2 the hyperplanes are
lines, and n(q-1)+1 equals 2q-1. The paper attributes the result to Jamison
and to Brouwer and Schrijver; this note makes no independent priority claim.

Theorem 6.1(c), manuscript page 14, states that a family of d hyperplanes
covering all but one point of a finite grid over a domain must have
d at least the sum of the coordinate cardinalities minus one in each
coordinate. It provides broader context for the polynomial method.

The Lean theorem uses the existing coordinate incidence model: graph lines
y=mx+b and vertical lines x=c. A blocking set B contains a point b0.
For each b in B other than b0, form the linear factor
1-(b.1-b0.1)u-(b.2-b0.2)v. Their product is one at the zero covector.
For every nonzero covector (u,v), the affine line
u(x-b0.1)+v(y-b0.2)=1 has a blocking point distinct from b0, which
annuls a product factor. Thus the product vanishes at all other covectors.
Its degree is at most |B|-1. Mathlib's finite-field grid evaluation-sum
theorem forces that degree to be at least 2(q-1), giving |B| at least 2q-1.
The two coordinate axes meet every line and contain exactly 2q-1 points.

This formalization proves the exact coordinate-plane minimum. It does not
assert a bound for arbitrary incidence planes, nonfield rings, selected
direction families, higher-dimensional spaces, or projective blocking sets.
The known finite-geometry theorem is attributed to the cited source; the
formal proof uses the existing Mathlib evaluation-sum theorem rather than
formalizing the full Alon--Furedi theorem or its general finite-grid bounds.
