# CHSH Square under Local Commutativity

## Abstract

Local commutativity collapses the algebraic CHSH square to four times the identity.

**Theorem 1.1 (Local commutativity collapses the CHSH square).**

$$\forall m, n,\ [\operatorname{Fintype}(m)] [\operatorname{DecidableEq}(m)] [\operatorname{Fintype}(n)] [\operatorname{DecidableEq}(n)],\ \forall A_{0}, A_{1}\in M_{m}(\mathbb{C}),\ \forall B_{0}, B_{1}\in M_{n}(\mathbb{C}),\ (\operatorname{Hermitian}(A_{0}) \land A_{0}^{2}=I_{m}) \land (\operatorname{Hermitian}(A_{1}) \land A_{1}^{2}=I_{m}) \land (\operatorname{Hermitian}(B_{0}) \land B_{0}^{2}=I_{n}) \land (\operatorname{Hermitian}(B_{1}) \land B_{1}^{2}=I_{n}) \land ((A_{0} A_{1}=A_{1} A_{0}) \lor (B_{0} B_{1}=B_{1} B_{0})) \Rightarrow \ \operatorname{let} S:=\operatorname{kronecker}(A_{0}, B_{0})+\operatorname{kronecker}(A_{0}, B_{1})+\operatorname{kronecker}(A_{1}, B_{0})-\operatorname{kronecker}(A_{1}, B_{1});\ S^{2}=4\cdot I_{m\times n}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lawrence J. Landau (1987). *On the violation of Bell's inequality in quantum theory*. DOI: [10.1016/0375-9601(87)90075-2](https://doi.org/10.1016/0375-9601(87)90075-2).

*Commentary.*

Let A0 and A1 and B0 and B1 be finite complex Hermitian involutions. If either the Alice pair or the Bob pair commutes, then the square of their CHSH matrix is four times the identity. The proof specializes LandauIdentity.landau_identity: the local commutation equality makes one commutator, and hence their Kronecker product, zero.

The acknowledged article's full text was not readable, so this repository-derived provenance does not claim that the article states this exact commuting-pair corollary.

This is only the algebraic square equality under a commuting local pair. It does not assert an expectation bound of two, an operator-norm CHSH bound of two, or any optimization over states.

## References

- Truth anchor: `D5/S3/QuantumBounds/LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes`
- Dependency: [D5/S3/QuantumBounds/LandauIdentity](LandauIdentity.md)
