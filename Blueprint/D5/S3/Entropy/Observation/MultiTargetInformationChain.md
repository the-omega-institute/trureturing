# Multi-Target Information Chain

## Abstract

The total finite information cost of adjoining a heterogeneous target family is independent of its order and is the sum of ordered conditional contributions.

**Theorem 1.1 (Total target information is independent of target order).**

$$\begin{gathered}\forall n: \mathbb{N}, X, B: \operatorname{Type},\\{}Y: \operatorname{Fin}\left(n\right) \to \operatorname{Type},\\{}(\operatorname{Fintype}\left(X\right) \land \operatorname{Fintype}\left(B\right) \land \forall i: \operatorname{Fin}\left(n\right), \operatorname{Fintype}\left(Y(i)\right)) \Rightarrow\\{}\forall mu: \operatorname{PMF}\left(X\right), C: X \to B,\\{}T: \forall i: \operatorname{Fin}\left(n\right), X \to Y(i),\\{}pi: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\\{}\operatorname{let} p_{0} := \operatorname{orderedCompletionLaw}\left(mu, C, T, \operatorname{refl}\left(\operatorname{Fin}\left(n\right)\right)\right),\\{}p_{pi} := \operatorname{orderedCompletionLaw}\left(mu, C, T, pi\right)\\{}\operatorname{in} \operatorname{H}\left(p_{0}\right) - \operatorname{H}\left(\operatorname{firstReadoutMarginal}\left(p_{0}\right)\right) = \sum_{k < n} \operatorname{prefixConditionalEntropy}\left(p_{pi}, k\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/MultiTargetInformationChain.multi_target_information_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each target value is tagged by its original finite index and placed after the concept readout in the repository's recursive FutureWord carrier. A permutation changes only the target coordinates and fixes the initial concept coordinate.

The frozen finite-word chain rule expands the permuted law into one full-prefix conditional entropy for each target. Entropy invariance under the induced coordinate equivalence identifies its total cost with the canonical target order.

The PMF binder supplies the finite probability model. No common target codomain is assumed: the family Y may vary with the target index.

## References

- Truth anchor: `D5/S3/Entropy/Observation/MultiTargetInformationChain.multi_target_information_chain`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/NamingWindow/FutureWordInformationChain](../NamingWindow/FutureWordInformationChain.md)
- Dependency: [D5/S3/Entropy/Relabeling/InjectiveInvariance](../Relabeling/InjectiveInvariance.md)
