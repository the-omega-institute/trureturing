# The exact two-dimensional criterion

## Abstract

An exact trace and determinant criterion for near order of positive two-dimensional matrices.

**Theorem 1.1 (Both directions, with the determinant condition).**

$$\forall L: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall W: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), ((\operatorname{PosDef}\left(L\right)) \land ((\operatorname{PosDef}\left(W\right)) \land (\operatorname{det}\left(L\right) = 1))) \Rightarrow ((\operatorname{NearOrder}\left(L, W\right)) \Leftrightarrow ((1 \le \operatorname{sqrt}\left(\operatorname{Re}\left(\operatorname{det}\left(W\right)\right)\right)) \land ((\operatorname{Re}\left(\operatorname{trace}\left(W\right)\right) + \operatorname{sqrt}\left(\operatorname{Re}\left(\operatorname{det}\left(W\right)\right)\right) \cdot \operatorname{Re}\left(\operatorname{trace}\left(L\right)\right))^{2} - (1 + \operatorname{sqrt}\left(\operatorname{Re}\left(\operatorname{det}\left(W\right)\right)\right))^{2} \cdot \left(\operatorname{Re}\left(\operatorname{trace}\left(L \cdot W\right)\right) + 2 \cdot \operatorname{sqrt}\left(\operatorname{Re}\left(\operatorname{det}\left(W\right)\right)\right)\right) \le 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HwangKimTwoDimensionalCriterion.near_order_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

L and W are positive definite complex 2×2 matrices and det L=1. Write d=√Re(det W), s=Re(tr W), t=Re(tr L), r=Re(tr(LW)) and E=(s+dt)²−(1+d)²(r+2d). The determinant of W is a positive real number, so d is its positive square root. The theorem is precisely NearOrder L W iff 1≤d and E≤0. No transport equation or scalar sign bridge is assumed in place of proving it for the actual mean.

The actual positive transport C=L⁻¹#W satisfies CLC=W. The original HwangKimNearOrderRefutation proof supplies det C=d and the two Cayley–Hamilton trace identities through a shared private helper. Positivity proves tr(LC)>0. The new sufficient direction uses the positive eigenvalues c₁,c₂ of C: c₁c₂≥1 and c₁+c₂≤1+c₁c₂ force both to be at least one. The determinant condition cannot be omitted. This is a criterion for arbitrary positive L,W in dimension two with det L=1; it is not restricted to either witness.

Source: the Ma–Zhang revision2 note, equation (criterion), full source retained at issue #29594, CC BY 4.0. Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: NUS and ChronoAI, Singapore. The original Hwang–Kim question is the final unnumbered display of arXiv:2407.07438v1 §6 p.17; equation (6.21) is a different proved comparison. This formalization is not a priority claim. Bhatia–Jain–Lim weak log-majorization and their norm/weak-majorization Conjecture 1 are not refuted by this criterion.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimTwoDimensionalCriterion.near_order_iff`
- Dependency: [D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation](HwangKimNearOrderRefutation.md)
