# Cubic pullback of the actual BKM integral

## Abstract

Cubic pullback of the actual BKM integral.

**Theorem 1.1 (The BKM integral at a positive definite cube).**

$$\left(\omega_{B^{3}}\right)\left(X\right) = \frac{1}{3}\cdot\left(B^{2} \cdot \left(\omega_{B}\right)\left(X\right) + B \cdot \left(\omega_{B}\right)\left(X\right) \cdot B + \left(\omega_{B}\right)\left(X\right) \cdot B^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMPowerPullback.omega_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let B be a positive definite complex matrix on any finite index type and let X be any complex matrix of the same size. Ω is the actual integral BKMRelativeDensity.omega, also used in PetzRotatedBKM. Its integrand at reference B is B to the power s, times X, times B to the power 1 − s, integrated from 0 to 1. The square and cube in the identity are ordinary matrix powers and 1/3 is a real scalar.

Rescale the integral at B³ by t = 3s and split [0, 3] into three unit intervals. Translating each interval back to [0, 1] factors out the ordered left and right powers of B.

In the quadratic entropy calculation for Wu’s Remark 3.15, equation (3.54), write U = Ω_B(V) for the Hermitian input tangent and A = B²U + BUB + UB² for its cube tangent. At Z = Tr(B³) > 0 and ρ = B³/Z, the normalized tangent is (A − ρ Tr(A))/Z. The cube identity, scalar homogeneity, and Ω_ρ(I) = ρ give its inverse BKM image 3V − (Tr(A)/Z)I. This supplies the tangent metric contribution. The full physical Hessian still requires differentiating the semigroup deficit along the physical path.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMPowerPullback.omega_cube`
- Dependency: [D5/S3/Quantum/Recovery/BKMObservableRigidity](BKMObservableRigidity.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMSpectralVariance](BKMSpectralVariance.md)
