# Averaging can reverse the determinant test

## Abstract

Exact rational determinant certificates for sharp-slice averaging.

In the original edge coordinates, the asymmetric vector is x=(49/10,14/5,2,49/10,6/5,2). Its C2 partner swaps a with c and b with d, retaining r and o; this swap comes from the vertex permutation (0 1)(2 3). Their coordinate average is (49/10,2,2,49/10,2,2), and every coordinate in both displayed vectors is greater than one. The original Gram determinant equals the character determinant under the orthogonal basis change, giving the same exact values 189/80 and -274999/10000. Thus even this actual coordinate average with its vertex-relabeling partner cannot certify a negative determinant for the original input from a negative determinant of the average.

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
