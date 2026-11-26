# Real-power interpolation in the physical odd frame

## Abstract

The real-power two-mode deficit interpolates between two physical occupation endpoints.

**Theorem 1.1 (Affine interpolation for each directed CAR trace).**

Lean statement: `D5/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit.mode_mixed_trace_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit.mode_mixed_trace_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Fix the odd basis (01, 10) and let a unitary U act on the even basis (00, 11). Write M(U) and N(U) for any two real aligned data sets in this frame. For either mode and either its lowering jump or its adjoint J, the real trace Re Tr(N(U) J* M(U) J) equals p times its value at diag(1, z) plus 1 − p times its value at the matrix with rows (0, −z) and (1, 0), where p = |U₀₀|² and z = det U. The two lowering sandwiches have crossing products proportional to zp and z(1 − p). Cyclicity gives the adjoint sandwiches by exchanging M and N.

**Theorem 1.2 (Exact real-power deficit interpolation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit.realPowerDeficit_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit.realPowerDeficit_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Fix real s and α, independent real projection and mixed-trace rates for both directions of each mode, and a real occupation diagonal for log D. Write P = Mˢ and Q = Mˢ⁻¹ using the real functional calculus and let h = Re Tr(P). The deficit is s(s/(s − 1))/4 times the difference between the weighted projection sum of Re Tr(P J*J) and the independently weighted mixed sum of Re Tr(Q J*M J), less α times [Re Tr(P log P) − h log h − Re Tr(P log D)]. The deficit at U is p times the deficit at the diagonal frame plus 1 − p times the deficit at the antidiagonal frame, with 0 ≤ p ≤ 1. Both frames have determinant z and preserve the first and second occupation, respectively.

Real functional calculus acts on the two real symmetric fibers in the same frame, including singular fibers. The mass and spectral-log term are independent of U. The individual jump projections and the Gibbs logarithm are diagonal in the fixed physical basis, so their pairings interpolate by the even diagonal entries.

Let L = |0⟩⟨1| and Z = diag(1, −1). In older-mode-first occupation order, the repository jumps modeJump 0 = L ⊗ I and modeJump 1 = −Z ⊗ L are the literal J₂ and −J₁ of WuPhysicalHighHigh. In Wu v1's recursive tensor order (mode 2, mode 1), the normalized CAR lowering letters in (3.22) for modes 1 and 2 are I ⊗ L and −L ⊗ Z, respectively, up to unit phase. The dissipative jumps in (3.24)–(3.27) match the repository literal jumps up to unit phase, with k = 0 for mode 2 and k = 1 for mode 1.

For Wu v1's physical deficit (3.54) at s > 1, take positive definite X, the product Gibbs density D, G = D^(1/(2s)), and M = GXG. Use log D for the occupation diagonal. For each mode's Gibbs factor diag(a, b) from (3.21), the lowering and adjoint projection weights are 2a and 2b, and the mixed weights are 2a(b/a)^(1/s) and 2b(a/b)^(1/s), respectively.

In the repository CAR convention the positive Wick generator uses Kₖ = modeJump k · (Z ⊗ Z). The unitary W = diag(1, i, i, 1) from WuAlignedCubicOrbit fixes D and G and obeys W modeJump k W* = iKₖ. The phase cancels in the dissipator. Since W* orbitMatrix(U,d) W = orbitMatrix(iU,d), apply the literal interpolation at iU and conjugate the endpoints back by W. The literal endpoints use −det U, with p fixed.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit.mode_mixed_trace_affine`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit.realPowerDeficit_affine`
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Matrix/SpectralPower.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuAlignedCubicOrbit](WuAlignedCubicOrbit.md)
