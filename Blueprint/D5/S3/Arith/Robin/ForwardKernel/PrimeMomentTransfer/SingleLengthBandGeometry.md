# Single-length band geometry

## Abstract

Polynomial bands retain the integer range and logarithmic bounds for single-length moments.

**Theorem 1.1 (Flooring with a strict exponent margin).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.floor_power_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.floor_power_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real beta<q with q>=0, all sufficiently large real Y satisfy Y^beta<=(floor Y)^q. The strict exponent margin absorbs the loss from flooring: Y^(beta-q) tends to zero, and floor Y>=Y/2 eventually. Both the quarter-power single-length range and the conjectural upper range use this shared bound.

**Theorem 1.2 (Integer cutoff and length ranges).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.band_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.band_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 0<alpha<beta<1/4. For all sufficiently large Y, uniformly over Y^alpha<=v<=Y^beta, let N and K be the natural floors of Y and v. Then N>=2, K>=1, N>=Y/2, K>=v/2, Y^(alpha/2)<=K<=Y^beta, K<=2*N^beta, and log N<=K<=N^(1/4). The quarter-power upper bound applies floor_power_upper with q=1/4. The doubled band permits the integer moment estimate to use the same exponent beta after flooring the cutoff.

**Theorem 1.3 (Uniform logarithmic comparison).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.band_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.band_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If beta<1, Y>1, and 1<=v<=Y^beta, then log(Y/v) is positive and lies between (1-beta)*log Y and log Y. The lower bound holds with the same positive factor 1-beta throughout the length band.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.band_geometry`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.band_log`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.floor_power_upper`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentAsymptotic](../FourthTransfer/FourthMomentAsymptotic.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling](RealLengthRescaling.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs](SingleLengthMSDefs.md)
