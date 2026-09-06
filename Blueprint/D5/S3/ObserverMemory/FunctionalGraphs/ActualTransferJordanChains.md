# Actual Transfer Jordan Chains

## Abstract

The transfer loss layers count actual Jordan chains on its transient Fitting summand.

**Theorem 1.1 (Actual chains realize the rank-loss profile).**

$$\forall Y \in Type, tau \in \operatorname{Function}\left(Y, Y\right),\; \operatorname{Finite}\left(Y\right) \Rightarrow \left(\exists I \in Type, hI \in \operatorname{Fintype}\left(I\right), s \in \operatorname{Function}\left(I, \operatorname{PNat}\left(\right)\right), b \in \operatorname{Basis}\left(\operatorname{Positions}\left(I, s\right), \operatorname{Complex}\left(\right), \operatorname{transientSubspace}\left(tau, \operatorname{card}\left(Y\right)\right)\right),\; \left(\forall m \in \operatorname{Nat}\left(\right), i \in I, j \in \operatorname{Fin}\left(\operatorname{s}\left(i\right)\right),\; \operatorname{apply}\left(\operatorname{pow}\left(\operatorname{transientTransfer}\left(tau, \operatorname{card}\left(Y\right)\right), m\right), \operatorname{b}\left(i, j\right)\right) = \operatorname{ite}\left(\operatorname{add}\left(j, m\right) < \operatorname{s}\left(i\right), \operatorname{b}\left(i, \operatorname{add}\left(j, m\right)\right), 0\right)\right) \land \left(\operatorname{Sizes}\left(I, s\right) = \operatorname{transferZeroBlocks}\left(tau\right) \land \left(\forall k \in \operatorname{Nat}\left(\right),\; 0 < k \Rightarrow \left(\left(\operatorname{informationLossLayer}\left(tau, k\right) = \operatorname{natSub}\left(\operatorname{finrank}\left(\operatorname{Complex}\left(\right), \operatorname{range}\left(\operatorname{pow}\left(\operatorname{transferOperator}\left(tau\right), \operatorname{pred}\left(k\right)\right)\right)\right), \operatorname{finrank}\left(\operatorname{Complex}\left(\right), \operatorname{range}\left(\operatorname{pow}\left(\operatorname{transferOperator}\left(tau\right), k\right)\right)\right)\right) \land \operatorname{informationLossLayer}\left(tau, k\right) = \operatorname{blockCountAtLeast}\left(\operatorname{Sizes}\left(I, s\right), k\right)\right) \land \left(\operatorname{blockCountExactly}\left(\operatorname{Sizes}\left(I, s\right), k\right) = \operatorname{natSub}\left(\operatorname{informationLossLayer}\left(tau, k\right), \operatorname{informationLossLayer}\left(tau, \operatorname{add}\left(k, 1\right)\right)\right) \land \operatorname{totalInformationLoss}\left(tau\right) = \operatorname{natSub}\left(\operatorname{card}\left(Y\right), \operatorname{card}\left(\operatorname{PeriodicCore}\left(tau\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FunctionalGraphs/ActualTransferJordanChains.information_loss_layers_from_actual_jordan_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Y and arbitrary self-map tau, work over the complex numbers and put n=card(Y). Positions(I,s) is the dependent sum of Fin(s(i)) over the finite type I, with s(i) positive. Sizes(I,s) is the multiset mapping s over all of I, retaining multiplicities. The basis belongs to transientSubspace(tau,n), the generalized zero-eigenspace. The conditional basis vector is used only when its index is in range. natSub means truncated natural subtraction and pred is the natural predecessor.

The general nilpotent chain theorem supplies the actual basis and iterate ranks. Rank-nullity computes its kernel tower; the existing finite tower uniqueness theorem identifies its positive size multiset with transferZeroBlocks(tau). Thus the profile in the existing information loss theorem now has a basis of actual chains. All four source equality leaves are retained. totalInformationLoss is the finite-support sum of positive loss layers, as defined by the existing finite-map theory.

## References

- Truth anchor: `D5/S3/ObserverMemory/FunctionalGraphs/ActualTransferJordanChains.information_loss_layers_from_actual_jordan_chains`
- Dependency: [D5/S1/Eigenstructure/NilpotentJordanChains](../../../S1/Eigenstructure/NilpotentJordanChains.md)
- Dependency: [D5/S3/ObserverMemory/FunctionalGraphs/InformationLossJordanLayers](InformationLossJordanLayers.md)
