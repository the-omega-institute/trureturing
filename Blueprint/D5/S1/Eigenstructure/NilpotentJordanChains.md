# Nilpotent Jordan Chains

## Abstract

Actual positive-length Jordan chains and all iterate ranks for a nilpotent operator.

**Theorem 1.1 (Every chain basis computes the power ranks).**

$$\forall K \in \operatorname{Type},\; \forall V \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] \forall f \in \operatorname{Module.End}\left(K, V\right),\; \forall s \in (I \to \operatorname{PNat}),\; \forall b \in \operatorname{Basis}\left((\Sigma (i : I), \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right)), K, V\right),\; (\forall m \in \mathbb{N},\; \forall i \in I,\; \forall j \in \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right),\; \left((f)^{m}\right)\left(b\left(\langle i, j\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(j\right) + m < \operatorname{val}\left(s\left(i\right)\right), b\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(j\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right))\rangle\right), 0\right)) \Rightarrow (\forall m \in \mathbb{N},\; \operatorname{Module.finrank}\left(K, \operatorname{LinearMap.range}\left((f)^{m}\right)\right) = \sum_{i : I} (\operatorname{val}\left(s\left(i\right)\right) - m))$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/NilpotentJordanChains.chain_basis_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite family of positive chain lengths and any basis with the displayed shift action, the range of the m-th power is spanned by the basis tails starting at position m. Their independence makes its dimension the sum of the remaining lengths. The basis index is the dependent sum of Fin(val(s(i))); subtraction of natural lengths is truncated.

**Theorem 1.2 (A chain basis computes every iterate rank).**

$$\forall K \in \operatorname{Type},\; \forall V \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall f \in \operatorname{Module.End}\left(K, V\right),\; (\operatorname{IsNilpotent}\left(f\right)) \Rightarrow (\exists I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] \exists s \in (I \to \operatorname{PNat}),\; \exists b \in \operatorname{Basis}\left((\Sigma (i : I), \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right)), K, V\right),\; (\forall m \in \mathbb{N},\; \forall i \in I,\; \forall j \in \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right),\; \left((f)^{m}\right)\left(b\left(\langle i, j\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(j\right) + m < \operatorname{val}\left(s\left(i\right)\right), b\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(j\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right))\rangle\right), 0\right)) \land (\forall m \in \mathbb{N},\; \operatorname{Module.finrank}\left(K, \operatorname{LinearMap.range}\left((f)^{m}\right)\right) = \sum_{i : I} (\operatorname{val}\left(s\left(i\right)\right) - m)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/NilpotentJordanChains.nilpotent_jordan_chains_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is any field and V is a finite-dimensional K-vector space. The finite index type I may be empty; each s(i) is a positive natural. The basis index is the dependent sum of Fin(val(s(i))) over i in I. The basis is ordered along each chain toward its terminal zero. In the conditional formula b(i,j+m) is used only when j+m is below s(i). Subtraction of natural lengths is truncated.

Mathlib's Module.torsion_by_prime_power_decomposition supplies the complete primary-decomposition induction over K[X]. Nilpotence makes Module.AEval' f torsion by powers of X. AdjoinRoot.powerBasis' gives the basis of each quotient K[X]/(X^s); polynomial linearity transports its shift to f. Removing empty quotient slots leaves positive lengths. The range of each iterate is proved equal to the span of the corresponding basis tails, whose independence computes its dimension. No algebraic closure, invariant complement, or preexisting Jordan basis is assumed.

## References

- Truth anchor: `D5/S1/Eigenstructure/NilpotentJordanChains.chain_basis_rank`
- Truth anchor: `D5/S1/Eigenstructure/NilpotentJordanChains.nilpotent_jordan_chains_rank`
