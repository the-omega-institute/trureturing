# Generic Finite Reciprocal-Product Sector Calculus

## Abstract

Generic finite reciprocal-product sector calculus

**Theorem 1.1 (Strict decrease in the height parameter).**

$$\operatorname{StrictAntiOn}\left(\operatorname{weight}\left(\right), \operatorname{Ioi}\left(\operatorname{threshold}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualHeightFourteenSector.strictAntiOn_weight_u` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive finite index size, every nonnegative shift family, and every p in the closed interval [0,1/4], the real part of the reciprocal product is strictly decreasing in u above the explicit threshold 4*(N+1)^2/pi^2. The proof supplies the reusable polar-angle positivity, u- and p-derivative signs, the endpoint continuity argument, and the signed-imaginary-part reduction. No six-pole constants or zeta data occur in this generic source.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualHeightFourteenSector.strictAntiOn_weight_u`
- Dependency: [D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds](ActualReciprocalSquareBounds.md)
