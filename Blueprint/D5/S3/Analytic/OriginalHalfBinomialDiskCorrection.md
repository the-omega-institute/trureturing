# The normalized native disk primitive

## Abstract

The same original period has a normalized holomorphic correction, continuation and nome.

**Definition 1.1 (The full unit disk).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D is the open ball with center zero and radius one in the complex plane.

**Definition 1.2 (The reciprocal Abel coefficient).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.R`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R(r)=1/((1-r)P(r) squared), where P is the literal original period. Its denominator is nonzero throughout D.

**Definition 1.3 (The removable native difference quotient).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.G`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G=dslope R 0, so its value at zero is the actual derivative of R at zero, and away from zero it is (R(r)-R(0))/r.

**Definition 1.4 (The normalized disk correction).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.H`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H is chosen from the disk primitive theorem with H(0)=0 and H prime equal to -iG/pi on D. Its restriction to D is uniquely determined; no regularity outside D is asserted.

**Theorem 1.5 (The normalized native disk primitive).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be the literal original half-binomial-square period on D={r: norm r<1}. The native Picard-Fuchs equation at zero and the literal constant series term give P(0)=1 and P' (0)=1/4. Hence R=1/((1-r)P squared) has R(0)=1 and R' (0)=1/2.

The removable difference quotient G=dslope R 0 is holomorphic on all of D, including zero. It satisfies G(0)=1/2 and rG(r)=R(r)-1. The disk primitive theorem gives H with H(0)=0 and H'=-iG/pi throughout D. In particular H' (0)=-i/(2pi). Any other normalized primitive with this derivative equals H on D, since the difference has zero derivative on the convex disk.

This same H determines the logarithmic continuation t0 and the native nome Q0. Its existence supplies actual functions used in those identities; no new period or arbitrary matching constant is introduced.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.G`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.H`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.R`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialDiskCorrection.disk_correction`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialWronskian](OriginalHalfBinomialWronskian.md)
