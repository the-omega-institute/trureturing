# Information-Loss Layers and Zero Jordan Chains

## Abstract

Observable loss layers are the rank drops and zero-block layers of a finite self-map.

**Theorem 1.1 (Information loss recovers every zero-block layer and its total).**

$$\forall Y \in Type, tau \in \operatorname{Function}\left(Y, Y\right), k \in \operatorname{Nat}\left(\right),\; \left(\operatorname{Finite}\left(Y\right) \land 0 < k\right) \Rightarrow \left(\left(\operatorname{informationLossLayer}\left(tau, k\right) = \operatorname{natSub}\left(\operatorname{finrank}\left(\operatorname{Complex}\left(\right), \operatorname{range}\left(\operatorname{pow}\left(\operatorname{transferOperator}\left(tau\right), \operatorname{pred}\left(k\right)\right)\right)\right), \operatorname{finrank}\left(\operatorname{Complex}\left(\right), \operatorname{range}\left(\operatorname{pow}\left(\operatorname{transferOperator}\left(tau\right), k\right)\right)\right)\right) \land \operatorname{informationLossLayer}\left(tau, k\right) = \operatorname{blockCountAtLeast}\left(\operatorname{transferZeroBlocks}\left(tau\right), k\right)\right) \land \left(\operatorname{blockCountExactly}\left(\operatorname{transferZeroBlocks}\left(tau\right), k\right) = \operatorname{natSub}\left(\operatorname{informationLossLayer}\left(tau, k\right), \operatorname{informationLossLayer}\left(tau, \operatorname{add}\left(k, 1\right)\right)\right) \land \operatorname{totalInformationLoss}\left(tau\right) = \operatorname{natSub}\left(\operatorname{card}\left(Y\right), \operatorname{card}\left(\operatorname{PeriodicCore}\left(tau\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FunctionalGraphs/InformationLossJordanLayers.information_loss_layers_and_zero_jordan_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau be a self-map of a finite carrier Y and let k be positive. The multiset transferZeroBlocks(tau) is constructed from consecutive rank-loss layers, rather than supplied as a parameter.

The k-th observable loss equals the drop between the preceding and current transfer ranks and also counts zero blocks of size at least k. Blocks of exact size k are the difference of consecutive loss layers.

The finite carrier stabilizes by card(Y), so totalInformationLoss is the finite support realization of the source's sum over all positive layers. It equals card(Y) minus the periodic-core card.

Theorem 8.3 is proved internally: the conjugate-partition construction has the same complete power-kernel tower as the canonical transfer operator. At the finite stabilization exponent, the Fitting transient subspace is that kernel, its restricted transfer is nilpotent, and every restricted power kernel is linearly equivalent to the corresponding ambient kernel. This binds the constructed multiset to the actual generalized zero-eigenspace. Mathlib's Nat-valued telescoping theorem supplies the total-loss summation step.

## References

- Truth anchor: `D5/S3/ObserverMemory/FunctionalGraphs/InformationLossJordanLayers.information_loss_layers_and_zero_jordan_chains`
- Dependency: [D5/S3/ContinuousObservables/TransientObservableFilter](../../ContinuousObservables/TransientObservableFilter.md)
- Dependency: [D5/S3/ObserverMemory/FunctionalGraphs/TraceRankJordanRecovery](TraceRankJordanRecovery.md)
