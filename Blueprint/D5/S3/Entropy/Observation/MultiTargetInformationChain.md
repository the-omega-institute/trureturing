# Multi-Target Information Chain

## Abstract

The total finite information cost of adjoining a heterogeneous target family is independent of its order and is the sum of ordered conditional contributions.

**Theorem 1.1 (The first marginal of a joint pushforward).**

$$\forall X: \operatorname{Type}, \forall A: \operatorname{Type}, \forall B: \operatorname{Type}, [\operatorname{Fintype}\left(X\right)] [\operatorname{Fintype}\left(B\right)] \forall mu: X \to \mathbb{R}, \forall f: X \to A, \forall g: X \to B, \operatorname{marginal}\left(\operatorname{pushforward}\left(x \mapsto (f(x), g(x)), mu\right)\right) = \operatorname{pushforward}\left(f, mu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/MultiTargetInformationChain.marginal_pushforward_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the joint law of two readouts over the second coordinate gives the law of the first readout. The coordinate marginal identity uses this equality, and the product contextuality construction applies it to finite restriction fibers.

**Theorem 1.2 (Total target information is independent of target order).**

$$\begin{gathered}\forall n: \mathbb{N}, X, B: \operatorname{Type},\\{}Y: \operatorname{Fin}\left(n\right) \to \operatorname{Type},\\{}(\operatorname{Fintype}\left(X\right) \land \operatorname{Fintype}\left(B\right) \land \forall i: \operatorname{Fin}\left(n\right), \operatorname{Fintype}\left(Y(i)\right)) \Rightarrow\\{}\forall mu: \operatorname{PMF}\left(X\right), C: X \to B,\\{}T: \forall i: \operatorname{Fin}\left(n\right), X \to Y(i),\\{}pi: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\\{}\operatorname{let} p_{0} := \operatorname{orderedCompletionLaw}\left(mu, C, T, \operatorname{refl}\left(\operatorname{Fin}\left(n\right)\right)\right),\\{}p_{pi} := \operatorname{orderedCompletionLaw}\left(mu, C, T, pi\right)\\{}\operatorname{in} \operatorname{H}\left(p_{0}\right) - \operatorname{H}\left(\operatorname{firstReadoutMarginal}\left(p_{0}\right)\right) = \sum_{k < n} \operatorname{prefixConditionalEntropy}\left(p_{pi}, k\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/MultiTargetInformationChain.multi_target_information_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each target value is tagged by its original finite index and placed after the concept readout in the repository's recursive FutureWord carrier. A permutation changes only the target coordinates and fixes the initial concept coordinate.

The frozen finite-word chain rule expands the permuted law into one full-prefix conditional entropy for each target. Entropy invariance under the induced coordinate equivalence identifies its total cost with the canonical target order.

The PMF binder supplies the finite probability model. No common target codomain is assumed: the family Y may vary with the target index.

## References

- Truth anchor: `D5/S3/Entropy/Observation/MultiTargetInformationChain.marginal_pushforward_pair`
- Truth anchor: `D5/S3/Entropy/Observation/MultiTargetInformationChain.multi_target_information_chain`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/NamingWindow/FutureWordInformationChain](../NamingWindow/FutureWordInformationChain.md)
- Dependency: [D5/S3/Entropy/Relabeling/InjectiveInvariance](../Relabeling/InjectiveInvariance.md)
