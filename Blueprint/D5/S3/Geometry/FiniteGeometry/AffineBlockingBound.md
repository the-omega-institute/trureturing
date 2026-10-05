# The sharp affine-plane blocking minimum

## Abstract

Affine blocking sets over a finite field of order q have sharp minimum 2q-1.

**Theorem 1.1 (Meeting every affine line requires exactly 2q-1 points).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/AffineBlockingBound.affine_blocking_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/AffineBlockingBound.affine_blocking_minimum` (`✓ std3`). ∎

*Citation.* Anurag Bishnoi, Pete L. Clark, Aditya Potukuchi and John R. Schmitt (2017). *On zeros of a polynomial in a finite grid*. DOI: [10.48550/arXiv.1508.06020](https://doi.org/10.48550/arXiv.1508.06020). URL: <https://arxiv.org/abs/1508.06020v2>.

*Commentary.*

For every finite field F of cardinality q, the least cardinality of a finite set B in F x F that intersects every graph line y = m*x+b and every vertical line x = c is 2*q-1. This includes nonprime field orders and characteristic two. The union of the two coordinate axes attains the minimum.

Choose b0 in B and multiply the factors 1-(b.1-b0.1)*u-(b.2-b0.2)*v for all other b in B. The product equals one at (u,v)=(0,0). Each nonzero covector defines the line u*(x-b0.1)+v*(y-b0.2)=1. A blocking point on this line differs from b0 and makes one factor zero, so the product vanishes at every other covector.

The degree is at most |B|-1. If |B|<2*q-1, Mathlib's finite-field evaluation-sum theorem says the sum of the product over all covectors is zero. Its actual values sum to one, a contradiction in every field. Hence |B|>=2*q-1.

Corollary 6.8 of Bishnoi, Clark, Potukuchi and Schmitt states the Jamison--Brouwer--Schrijver minimum n*(q-1)+1 in affine dimension n. The declaration proves its exact two-dimensional coordinate case. It does not cover arbitrary incidence planes, rings, projective blocking sets or only selected directions; Theorem 6.1(c) of the source gives the broader finite-grid hyperplane-covering context.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/AffineBlockingBound.affine_blocking_minimum`
- Dependency: [D5/S3/Geometry/FiniteGeometry/AffinePlaneLines](AffinePlaneLines.md)
