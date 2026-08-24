# Support Gap Target Law

## Abstract

A target branch outside behavior support admits data-equivalent transition models with different target laws.

**Theorem 1.1 (Missing behavior support leaves the target law undetermined).**

$$\operatorname{TargetBranchMass}(pi, h, a) \neq 0 \land \operatorname{BehaviorMass}(mu, h, a) = 0 \land yZero \neq yOne \Rightarrow\\{}\exists M, N,\\{}\operatorname{Transition}(M, h, a) \neq \operatorname{Transition}(N, h, a) \land\\{}(\forall hPrime, aPrime, \operatorname{BehaviorMass}(mu, hPrime, aPrime) \neq 0 \Rightarrow \operatorname{Transition}(M, hPrime, aPrime) = \operatorname{Transition}(N, hPrime, aPrime)) \land\\{}\operatorname{TargetOutcomeLaw}(pi, M) \neq \operatorname{TargetOutcomeLaw}(pi, N).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/SupportGapTargetLaw.support_gap_target_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target branch law gives positive mass to the selected history-action pair, while the behavior policy assigns zero mass to its action at that history.

The first transition mechanism is constant. The second changes only the unsupported selected branch, so the two mechanisms agree at every branch carrying nonzero behavior mass.

Pushing the target branch law through the mechanisms yields different outcome laws: the positive selected atom reaches the distinct second outcome only under the second mechanism.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/SupportGapTargetLaw.support_gap_target_law`
