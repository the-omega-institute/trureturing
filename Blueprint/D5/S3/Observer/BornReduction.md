# Rank-One Born Reduction

## Abstract

A rank-one record branch on a rank-one pure state is exactly a squared transition modulus.

**Theorem 1.1 (Rank-one pure-state record weight is a squared transition modulus).**

$$\forall n, \kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\ \forall P: \kappa \to M_{n}(\mathbb{C}),\ \rho \in M_{n}(\mathbb{C}),\ k \in \kappa,\ \varphi, \psi \in \mathbb{C}^{n},\\ \operatorname{Record}(P) \land P_{k}=\varphi \varphi^{*} \land \rho = \psi \psi^{*} \land \langle \varphi, \varphi \rangle=1 \land \langle \psi, \psi \rangle=1 \Rightarrow\\ w_{k}(\rho)=\lvert \langle \varphi, \psi \rangle \rvert^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BornReduction.rank_one_pure_state_modulus_square_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix one branch k of a finite family P. If its matrix is the rank-one outer product of phi, while rho is the rank-one outer product of psi, then the record weight trace(rho P_k) is exactly the squared modulus of their transition inner product. No measurement axioms or normalization hypotheses are consumed; for unit vectors the right-hand side is the Born branch probability. The equality is exact over the complex numbers, with no approximation or residual term.

## References

- Truth anchor: `D5/S3/Observer/BornReduction.rank_one_pure_state_modulus_square_reduction`
- Dependency: [D5/S3/Observer/Conditioning](Conditioning.md)
