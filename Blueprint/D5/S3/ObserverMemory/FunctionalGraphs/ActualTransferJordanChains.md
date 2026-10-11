# Actual Transfer Jordan Chains

## Abstract

The transfer loss layers count actual Jordan chains on its transient Fitting summand.

**Theorem 1.1 (Actual chains realize the rank-loss profile).**

$$\forall Y \in \operatorname{Type},\; [\operatorname{Finite}\left(Y\right)] \forall tau \in (Y \to Y),\; \exists I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] \exists s \in (I \to \operatorname{PNat}),\; \exists b \in \operatorname{Basis}\left((\Sigma (i : I), \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right)), \mathbb{C}, \operatorname{transientSubspace}\left(tau, \operatorname{Nat.card}\left(Y\right)\right)\right),\; (\forall m \in \mathbb{N},\; \forall i \in I,\; \forall j \in \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right),\; \left((\operatorname{transientTransfer}\left(tau, \operatorname{Nat.card}\left(Y\right)\right))^{m}\right)\left(b\left(\langle i, j\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(j\right) + m < \operatorname{val}\left(s\left(i\right)\right), b\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(j\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right))\rangle\right), 0\right)) \land ((\operatorname{Multiset.map}\left(s, \operatorname{val}\left((\operatorname{Finset.univ} : \operatorname{Finset}\left(I\right))\right)\right) = \operatorname{transferZeroBlocks}\left(tau\right)) \land (\forall k \in \mathbb{N},\; (0 < k) \Rightarrow (((\operatorname{informationLossLayer}\left(tau, k\right) = \operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{LinearMap.range}\left((\operatorname{transferOperator}\left(tau\right))^{\operatorname{Nat.pred}\left(k\right)}\right)\right) - \operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{LinearMap.range}\left((\operatorname{transferOperator}\left(tau\right))^{k}\right)\right)) \land (\operatorname{informationLossLayer}\left(tau, k\right) = \operatorname{blockCountAtLeast}\left(\operatorname{Multiset.map}\left(s, \operatorname{val}\left((\operatorname{Finset.univ} : \operatorname{Finset}\left(I\right))\right)\right), k\right))) \land ((\operatorname{blockCountExactly}\left(\operatorname{Multiset.map}\left(s, \operatorname{val}\left((\operatorname{Finset.univ} : \operatorname{Finset}\left(I\right))\right)\right), k\right) = \operatorname{informationLossLayer}\left(tau, k\right) - \operatorname{informationLossLayer}\left(tau, k + 1\right)) \land (\operatorname{totalInformationLoss}\left(tau\right) = \operatorname{Nat.card}\left(Y\right) - \operatorname{Nat.card}\left(\operatorname{PeriodicCore}\left(tau\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FunctionalGraphs/ActualTransferJordanChains.information_loss_layers_from_actual_jordan_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Y and arbitrary self-map tau, work over the complex numbers and put n=Nat.card(Y). The basis index is the dependent sum of Fin(val(s(i))) over the finite type I, with s(i) positive. The lengths form the multiset mapping s over Finset.univ.val, retaining multiplicities. The basis belongs to transientSubspace(tau,n), the generalized zero-eigenspace. The conditional basis vector is used only when its index is in range. Subtraction of natural numbers is truncated; Nat.pred is the natural predecessor.

The general nilpotent chain theorem supplies the actual basis and iterate ranks. Rank-nullity computes its kernel tower; the existing finite tower uniqueness theorem identifies its positive size multiset with transferZeroBlocks(tau). Thus the profile in the existing information loss theorem now has a basis of actual chains. All four source equality leaves are retained. totalInformationLoss is the finite-support sum of positive loss layers, as defined by the existing finite-map theory.

## References

- Truth anchor: `D5/S3/ObserverMemory/FunctionalGraphs/ActualTransferJordanChains.information_loss_layers_from_actual_jordan_chains`
- Dependency: [D5/S1/Eigenstructure/NilpotentJordanChains](../../../S1/Eigenstructure/NilpotentJordanChains.md)
- Dependency: [D5/S3/ObserverMemory/FunctionalGraphs/InformationLossJordanLayers](InformationLossJordanLayers.md)
