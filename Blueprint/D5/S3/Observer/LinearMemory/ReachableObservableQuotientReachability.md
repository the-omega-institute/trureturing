# Reachable Observable Quotient Reachability

## Abstract

The reachable-observable quotient is spanned by the canonical images of input iterates.

**Theorem 1.1 (The minimal quotient remains reachable).**

$$\begin{gathered}\forall K, V, U, Y: Type, A, B, C,\\{}\operatorname{DivisionRing}(K) \land \operatorname{AddCommGroup}(V) \land \operatorname{Module}(K, V) \land \operatorname{AddCommGroup}(U) \land \operatorname{Module}(K, U),\\{}\operatorname{AddCommGroup}(Y) \land \operatorname{Module}(K, Y) \land A \in \operatorname{LinearMap}(K, V, V) \land B \in \operatorname{LinearMap}(K, U, V) \land C \in \operatorname{LinearMap}(K, V, Y) \Rightarrow\\{}\operatorname{let}(R, \operatorname{reachableSubspace}(A, B)), \operatorname{let}(Nfuture, \operatorname{comap}(\operatorname{eventualKernel}(C, A), \operatorname{subtype}(R))),\\{}\operatorname{span}(K, \{\operatorname{mkQ}(Nfuture, \operatorname{reachableGenerator}(A, B, k, u)) \mid k \in N, u \in U\}) = top.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ReachableObservableQuotientReachability.reachable_observable_quotient_is_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reachable carrier is constructed as the span of the actual input directions and their dynamics iterates. Span induction carries those generators through the canonical quotient by the imported all-future invisible subspace.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/ReachableObservableQuotientReachability.reachable_observable_quotient_is_reachable`
- Dependency: [D5/S3/Observer/LinearMemory/ZeroMemoryCriterion](ZeroMemoryCriterion.md)
