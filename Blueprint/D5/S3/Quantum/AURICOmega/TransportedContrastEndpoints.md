# Two reflected differences in a four-point Gram form

## Abstract

What does the reflected fourth point tell us about the difference of two readings?

**Theorem 1.1 (A determinant bound at every overlap).**

Lean statement: `D5/S3/Quantum/AURICOmega/TransportedContrastEndpoints.reflected_contrast_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TransportedContrastEndpoints.reflected_contrast_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a symmetric rational kernel with diagonal entries one. Suppose the ternary operation satisfies [a,a,b] = b and [a,b,b] = a, and the kernel is invariant under common left and right translations. Assume the Gram form of every four-point sample is nonnegative for all rational weights. Sample points may repeat.

For any x, y and z put w = [x,z,y]. Translating the pair (z,y) on the left gives (x,w), and translating (z,x) on the right gives (y,w). Symmetry therefore gives k(x,w) = k(y,z) and k(y,w) = k(x,z).

Write d = k(x,z) − k(y,z), A = 1 − k(x,y), and C = 1 − k(z,w). On (x,y,z,w) the weights (u,−u,v,−v) give twice the binary form Au² + 2duv + Cv². Its diagonal coefficients and its determinant are nonnegative, so d² ≤ AC. When either diagonal coefficient vanishes, the same inequality forces d = 0.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/TransportedContrastEndpoints.reflected_contrast_sq_le`
