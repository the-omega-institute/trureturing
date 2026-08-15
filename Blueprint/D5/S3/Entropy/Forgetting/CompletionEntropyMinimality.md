# Conditional Entropy under Completion Factorization

## Abstract

A deterministic completion that factors through another has no more conditional entropy under the same observation.

**Theorem 1.1 (A factorized completion has no more conditional entropy).**

$$\begin{gathered}\operatorname{ProbabilityLaw}(p),\\\operatorname{Surjective}(factor),\\completion = factor \circ otherCompletion \Rightarrow\\H_{p}(completion(Y) \mid observation(Y)) \leq H_{p}(otherCompletion(Y) \mid observation(Y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/CompletionEntropyMinimality.completion_conditional_entropy_le_of_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a normalized nonnegative mass function on a finite initial-state carrier Y. The maps observation : Y -> O and otherCompletion : Y -> W give the observed and refined records. Suppose factor : W -> Z is surjective and completion = factor composed with otherCompletion. Then the conditional entropy of completion(Y) given observation(Y) is at most the conditional entropy of otherCompletion(Y) given the same observation.

This factorization is the formal universal-property premise behind the source's minimal exact completion: every competing exact deterministic completion supplies a refinement from which the minimal completion is recovered deterministically. Surjectivity records that both finite completion carriers contain only reachable record values.

The proof pushes the refined joint law through the first-coordinate-preserving map (o, w) -> (o, factor(w)). The imported deterministic-forgetting theorem lowers its joint entropy, while an explicit finite-sum identity shows that the observation marginal is unchanged. Applying the entropy chain rule to both joint laws cancels that common marginal and gives the claimed conditional-entropy inequality. Library and repository searches found no exact theorem to bind.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/CompletionEntropyMinimality.completion_conditional_entropy_le_of_factorization`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](CapacityMonotone.md)
