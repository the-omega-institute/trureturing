# Native Correction Joint Finite Support

## Abstract

An exact state-dependent finite support for the full native correction expansion on every original actual tensor.

The support is dependent over the original correction shift, the full oscillator monomial, and the signed mode tuple for that monomial. It retains the original exponent+2*shift, the complete normalSplitCoefficient, every repeated occurrence, and the arbitrary ActualTensor target. No global mode cutoff, positivity assumption, distinguished-variable inversion, or replacement operator is introduced.

**Theorem 1.1 (Actual Native Correction Joint Finite Action).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockNativeJointSupport.actual_native_correction_joint_finite_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockNativeJointSupport.actual_native_correction_joint_finite_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice datum, determinant witness, charge, correction polynomial, integer exponent, oscillator polynomial, and arbitrary actual tensor, the native correction coefficient is a finite sum over one dependent index carrying all three coordinates: shift, oscillator monomial, and signed split modes. Outside that single finite set the exact native term is zero, and the coefficient is exactly the finite sum of those terms.

The proof obtains state-dependent finite mode support for each already-supported shift and monomial, then packages the supports with Finset.sigma. The dependent regrouping is performed by Finset.sum_sigma'; no exchange of unsupported signed-mode and cut sums is used. This is the required joint support statement beyond the earlier aggregated finite-action theorem.

This theorem identifies only the valid finite regrouping of the native correction expansion. Matching its terms with the full original Lambda/commonKernel diagonal, including creation and annihilation factors, the checked scalar and ground normalizations, the single cocycle, the genuine recurrence and initials, and both unchanged all-j identities remains open. The larger VOA/CFT, anomaly/fusion, string, and AdS/CFT objectives remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockNativeJointSupport.actual_native_correction_joint_finite_action`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockNativeNormalActions](LatticeHalfFockNativeNormalActions.md)
