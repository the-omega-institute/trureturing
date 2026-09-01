# Ramified Five Matrix Reduction

## Abstract

An integral matrix that squares to five times the identity is nonnilpotent over the integers and invertible over the rationals, but its reduction at the ramified prime five is square-zero.

**Theorem 1.1 (Reduction at five turns an integral square root of five nilpotent).**

$$\begin{aligned}\forall n \in \mathbb{N}, n \geq 1, \forall J \in \operatorname{M}(n, \mathbb{Z}), J^2 = 5\operatorname{I}(n) \Rightarrow\\{}\operatorname{reduceFive}(J)^2 = 0 \land \operatorname{IsNilpotent}(\operatorname{reduceFive}(J)) \land\\{}\operatorname{charpoly}(\operatorname{reduceFive}(J)) = X^n \land \operatorname{trace}(\operatorname{reduceFive}(J)) = 0 \land\\{}\operatorname{det}(\operatorname{reduceFive}(J)) = 0 \land \operatorname{det}(J)^2 = 5^n \land\\{}\neg\operatorname{IsNilpotent}(J) \land \operatorname{IsUnitOverRationals}(J).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RamifiedFiveMatrixReduction.ramified_five_matrix_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping the identity J^2=5I_n through the explicit ring homomorphism from the integers to ZMod five sends the right-hand side to zero. Multiplicativity of matrix mapping then gives Jbar^2=0. Standard nilpotent-matrix identities force the characteristic polynomial, trace, and determinant conclusions.

Taking determinants before reduction gives det(J)^2=5^n, which is nonzero because n is positive. Thus J cannot be nilpotent over the integers, and its determinant remains nonzero over the rationals, where the matrix is invertible. This contrast is the ramification phenomenon captured by the theorem.

The concrete witness J=((0,5),(1,0)) has determinant -5 and reduces to ((0,0),(1,0)). The Lean module also proves that an integral compatibility relation J^T G=GJ survives reduction and applies the theorem to the integral Hodge matrix on Lambda^2 A4.

## References

- Truth anchor: `D5/S3/Arith/Lattices/RamifiedFiveMatrixReduction.ramified_five_matrix_reduction`
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](ExactDualLatticeFormula.md)
