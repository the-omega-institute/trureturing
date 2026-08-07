# Landau Identity for Finite Matrix Observables

## Abstract

The algebraic Landau identity for the finite-dimensional CHSH operator.

**Theorem 1.1 (The CHSH square is governed by local commutators).**

$$\forall m, n,\ [\operatorname{Fintype}(m)] [\operatorname{DecidableEq}(m)] [\operatorname{Fintype}(n)] [\operatorname{DecidableEq}(n)],\ \forall A_{0}, A_{1}\in M_{m}(\mathbb{C}),\ \forall B_{0}, B_{1}\in M_{n}(\mathbb{C}),\ (\operatorname{Hermitian}(A_{0}) \land A_{0}^{2}=I_{m}) \land (\operatorname{Hermitian}(A_{1}) \land A_{1}^{2}=I_{m}) \land (\operatorname{Hermitian}(B_{0}) \land B_{0}^{2}=I_{n}) \land (\operatorname{Hermitian}(B_{1}) \land B_{1}^{2}=I_{n}) \Rightarrow \operatorname{let} S:=\operatorname{kronecker}(A_{0}, B_{0})+\operatorname{kronecker}(A_{0}, B_{1})+\operatorname{kronecker}(A_{1}, B_{0})-\operatorname{kronecker}(A_{1}, B_{1}),\ C:=-\operatorname{kronecker}((A_{0} A_{1}-A_{1} A_{0}), (B_{0} B_{1}-B_{1} B_{0}));\ S^{2}=4\cdot I_{m\times n}+C$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LandauIdentity.landau_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m and n be finite index types with decidable equality. Let A0 and A1 be Hermitian involutions in the m-by-m complex matrices, and let B0 and B1 be Hermitian involutions in the n-by-n complex matrices. For the displayed CHSH matrix S, its square is four times the identity plus C, where C is the negative Kronecker product of the two local commutators. The declaration proves this exact matrix equality. Hermiticity records the observable context, while the proof uses only the four involution equations. This is the algebraic kernel only: it introduces no state or variance, proves no positivity or norm estimate, and does not establish the three-gap decomposition, its saturation conditions, or the Tsirelson bound.

## References

- Truth anchor: `D5/S3/QuantumBounds/LandauIdentity.landau_identity`
