# The actual original ratio on the full lens

## Abstract

The same original period has a normalized holomorphic correction, continuation and nome.

**Definition 1.1 (The principal slit disk).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialContinuation.slitDisk`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialContinuation.slitDisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The slit disk is D intersect the complex principal-logarithm slit plane.

**Definition 1.2 (The full complementary-period overlap).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialContinuation.lens`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialContinuation.lens` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lens is the intersection of the radius-one open disks centered at zero and one.

**Definition 1.3 (The normalized logarithmic continuation).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialContinuation.t0`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialContinuation.t0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

t0(r)=(i/pi)(log(16)-log(r))+H(r), with the actual normalized native primitive H.

**Definition 1.4 (The actual continued numerator).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialContinuation.n0`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialContinuation.n0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

n0(r)=P(r)t0(r). On the full lens it equals the original complementary numerator iP(1-r).

**Theorem 1.5 (The actual original ratio on the full lens).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialContinuation.actual_continuation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialContinuation.actual_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On U=D intersect the principal logarithm slit plane, set t0=(i/pi)(log(16)-log(r))+H(r). The identity rG=R-1 gives the actual derivative t0'=-i/(pi r(1-r)P squared) everywhere on U.

The full lens L={norm r<1 and norm(1-r)<1} is open and convex and lies in U: norm(1-r)<1 implies Re(r)>0. The native tau has exactly the same derivative there, so t0-tau is constant on L. The constant is fixed by the original complementary-period log(16) limit, not by an assumed continuation.

The reciprocal period has a finite derivative at zero, so (1/P(r)-1)/r has a finite real radial limit. Multiplication by r log(r), tending to zero, pays the necessary logarithmic period error. Thus pi P(1-r)/P(r)+log(r)-log(16) tends to zero along positive real r, using reality from the original Euler integral. H(r) tends to zero, which makes the constant difference zero. The resulting equality holds at every complex point of L.

**Theorem 1.6 (The continued native numerator and its equation).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialContinuation.continued_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialContinuation.continued_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual function n0=P t0 is holomorphic on the entire slit disk U and equals iP(1-r) on the full lens. Its actual first and second derivatives satisfy r(1-r)n0''+(1-2r)n0'-n0/4=0 and the oriented Wronskian n0'P-n0P'=-i/(pi r(1-r)) throughout U.

The proof differentiates the neighborhood identity r(1-r)P squared t0'=-i/pi, then combines it with the actual native Picard-Fuchs equation for P. Holomorphy on the open domain supplies the derivative regularity, and a neighborhood product identity supplies the actual second derivative of n0.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialContinuation.actual_continuation`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialContinuation.continued_numerator`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialContinuation.lens`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialContinuation.n0`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialContinuation.slitDisk`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialContinuation.t0`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialDiskCorrection](OriginalHalfBinomialDiskCorrection.md)
