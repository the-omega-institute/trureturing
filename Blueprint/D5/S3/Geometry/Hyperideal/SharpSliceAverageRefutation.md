# Averaging can reverse the determinant test

## Abstract

Exact rational determinant certificates for sharp-slice averaging.

Use the fixed character-coordinate Gram matrix gram with slot order (12,13,14,34,24,23). The asymmetric vector has parameters (r,o,A,B,xi,zeta)=(49/10,49/10,2,2,4/5,0), while its C2 average has the same first four parameters and xi=zeta=0.

**Theorem 1.1 (Exact determinant reversal).**

$$\neg \left(\operatorname{det}\left(\operatorname{gram}\left(\frac{49}{10}, \frac{49}{10}, 2, 2, 0, 0\right)\right) < 0 \Rightarrow \operatorname{det}\left(\operatorname{gram}\left(\frac{49}{10}, \frac{49}{10}, 2, 2, \frac{4}{5}, 0\right)\right) < 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SharpSliceAverageRefutation.sharp_slice_average_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement refutes the implication that a negative determinant for the averaged vector forces a negative determinant for the asymmetric vector. The averaged value is -274999/10000 and the asymmetric value is 189/80.

Both values are exact rational evaluations of the displayed finite Gram determinant, so the reversal does not rely on a numerical approximation or on a global realization claim.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SharpSliceAverageRefutation.sharp_slice_average_refutation`
- Dependency: [D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder](SixIndependentLengthRemainder.md)
