# Nonlinear skew rigidity

## Abstract

A product identity and a strict norm contraction force an arbitrary total map to be real linear and skew.

The carrier is any real inner product space, including the zero space and spaces that are incomplete or infinite dimensional. The map is initially a total function. No continuity, additivity or scalar compatibility is assumed. Its norm is a fixed positive factor less than one times the input norm. For each pair of inputs, the sum of their inner product and their output inner product, multiplied by the sum of the two mixed inner products, is zero.

**Theorem 1.1 (The original map is linear, skew and has a fixed negative square).**

Lean statement: `D5/S3/Geometry/NonlinearSkewRigidity.nonlinear_skew_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/NonlinearSkewRigidity.nonlinear_skew_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion concerns the same given function F: it preserves addition and multiplication by every real scalar, the inner product of F(y) with z is minus the inner product of y with F(z), and F(F(y)) is minus r squared times y. The orthogonality premise is retained in the statement. The zero carrier is handled separately. Around every nonzero vector v there is a positive epsilon such that the ball of radius three epsilon is strictly acute with margin r squared. Cauchy-Schwarz bounds the output inner product, so the first product factor is positive and the mixed factor vanishes throughout that ball. Subtracting the resulting skew identities at v+h and v gives the exact identity: the inner product of b with F(v+h)-F(v) equals minus the inner product of F(b) with h, for h of norm less than epsilon and b in the epsilon ball about v. Only the known inner product and norm enter the continuity argument. For any w, scaling w into this small ball and rescaling its difference gives a vector q with inner product against each b equal to minus the inner product of F(b) with w. An open ball separates vectors, so q is unique. This same identity proves additivity and real scalar compatibility of the assignment w to q, defining a genuine linear map T. Local skewness gives F=T on the ball. A linear functional vanishing on an open set vanishes everywhere, which extends skewness of T globally. The norm equations at v, v+h and v-h give the exact norm scale for small h; linear rescaling gives it for every vector. For fixed nonzero z the original product identity on the ball becomes the product of the inner products of b with z-T(F(z)) and with F(z)-T(z). The first vector is nonzero because r squared is less than one. Its linear functional is nonzero on a nonempty open part of the ball, forcing the second vector to vanish. The norm equation handles z=0. Polarizing the global norm identity and using skewness proves the square formula. No limit of F, completion of the carrier or finite-dimensional representation is used.

## References

- Truth anchor: `D5/S3/Geometry/NonlinearSkewRigidity.nonlinear_skew_rigidity`
