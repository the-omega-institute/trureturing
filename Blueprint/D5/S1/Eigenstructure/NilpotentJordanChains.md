# Nilpotent Jordan Chains

## Abstract

Actual positive-length Jordan chains and all iterate ranks for a nilpotent operator.

**Theorem 1.1 (A chain basis computes every iterate rank).**

$$\forall K \in Type, V \in Type, f \in \operatorname{End}\left(K, V\right),\; \left(\operatorname{Field}\left(K\right) \land \left(\operatorname{AddCommGroup}\left(V\right) \land \left(\operatorname{Module}\left(K, V\right) \land \left(\operatorname{FiniteDimensional}\left(K, V\right) \land \operatorname{IsNilpotent}\left(f\right)\right)\right)\right)\right) \Rightarrow \left(\exists I \in Type, hI \in \operatorname{Fintype}\left(I\right), s \in \operatorname{Function}\left(I, \operatorname{PNat}\left(\right)\right), b \in \operatorname{Basis}\left(\operatorname{Positions}\left(I, s\right), K, V\right),\; \left(\forall m \in \operatorname{Nat}\left(\right), i \in I, j \in \operatorname{Fin}\left(\operatorname{s}\left(i\right)\right),\; \operatorname{apply}\left(\operatorname{pow}\left(f, m\right), \operatorname{b}\left(i, j\right)\right) = \operatorname{ite}\left(\operatorname{add}\left(j, m\right) < \operatorname{s}\left(i\right), \operatorname{b}\left(i, \operatorname{add}\left(j, m\right)\right), 0\right)\right) \land \left(\forall m \in \operatorname{Nat}\left(\right),\; \operatorname{finrank}\left(K, \operatorname{range}\left(\operatorname{pow}\left(f, m\right)\right)\right) = \sum_{i \in I} \operatorname{natSub}\left(\operatorname{s}\left(i\right), m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/NilpotentJordanChains.nilpotent_jordan_chains_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is any field and V is a finite-dimensional K-vector space. The finite index type I may be empty; each s(i) is a positive natural. Positions(I,s) denotes the dependent sum of Fin(s(i)) over i in I. The basis is ordered along each chain toward its terminal zero. In the conditional formula b(i,j+m) is used only when j+m is below s(i). natSub is truncated natural subtraction.

Mathlib's Module.torsion_by_prime_power_decomposition supplies the complete primary-decomposition induction over K[X]. Nilpotence makes Module.AEval' f torsion by powers of X. AdjoinRoot.powerBasis' gives the basis of each quotient K[X]/(X^s); polynomial linearity transports its shift to f. Removing empty quotient slots leaves positive lengths. The range of each iterate is proved equal to the span of the corresponding basis tails, whose independence computes its dimension. No algebraic closure, invariant complement, or preexisting Jordan basis is assumed.

## References

- Truth anchor: `D5/S1/Eigenstructure/NilpotentJordanChains.nilpotent_jordan_chains_rank`
