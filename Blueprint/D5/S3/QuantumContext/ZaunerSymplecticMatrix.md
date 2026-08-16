# An Exact Modular Zauner-Matrix Certificate

## Abstract

An explicit modular Zauner matrix has order three and fixes the displayed residue vector.

**Theorem 1.1 (The displayed modular Zauner matrix has order three and a fixed vector).**

$$S=\begin{pmatrix}6&23\\19&17\end{pmatrix}, v=(8, 16),\\\operatorname{det}(S)=1 \land \operatorname{tr}(S)=-1 \land\\S^{2}+S+I=0 \land S^{3}=I \land S\neq I \land Sv=v.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ZaunerSymplecticMatrix.zauner_symplectic_matrix_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be the matrix with rows (6,23) and (19,17) over Z/24Z, and let v=(8,16). Exact residue arithmetic gives det(S)=1 and tr(S)=-1. The matrix satisfies S^2+S+I=0 and S^3=I, while S is not the identity, so its order is exactly three. Direct matrix-vector multiplication gives Sv=v.

The pinned mathlib search found the general two-by-two determinant and trace formulas, which the Lean proof applies before reducing the finite residue equalities in the kernel. No unchecked evaluator, native_decide, numerical approximation, or private axiom is used.

This is an instance-level certificate for the explicit matrix and fixed vector in the source clause. It does not formalize the exhaustive GL(2,Z/24Z) search, identify the full value-preserving group with Z/6Z, or rule out additional antiunitary symmetries.

## References

- Truth anchor: `D5/S3/QuantumContext/ZaunerSymplecticMatrix.zauner_symplectic_matrix_certificate`
