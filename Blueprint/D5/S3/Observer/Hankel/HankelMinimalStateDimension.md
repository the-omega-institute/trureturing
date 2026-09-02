# Hankel Minimal State Dimension

## Abstract

Every finite-dimensional realization with the same Markov parameters has dimension at least the stable Hankel rank. The named reachable-observable quotient realization attains that minimum, while raw state dimension is presentation-dependent.

**Theorem 1.1 (The Hankel rank is the minimum realization dimension).**

$$\begin{gathered}\forall K, V, V', U, Y: Type,\\{}\operatorname{Field}(K) \land \operatorname{AddCommGroup}(V) \land \operatorname{Module}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{AddCommGroup}(V') \land \operatorname{Module}(K, V') \land \operatorname{FiniteDimensional}(K, V') \land\\{}\operatorname{AddCommGroup}(U) \land \operatorname{Module}(K, U) \land \operatorname{AddCommGroup}(Y) \land \operatorname{Module}(K, Y) \land\\{}A \in \operatorname{LinearMap}(K, V, V) \land B \in \operatorname{LinearMap}(K, U, V) \land C \in \operatorname{LinearMap}(K, V, Y),\\{}A' \in \operatorname{LinearMap}(K, V', V') \land B' \in \operatorname{LinearMap}(K, U, V') \land C' \in \operatorname{LinearMap}(K, V', Y),\\{}\forall k \in N, \operatorname{markovParameter}(A', B', C', k) = \operatorname{markovParameter}(A, B, C, k),\\{}r, s \in N, \operatorname{finrank}(K, V) \leq r \land \operatorname{finrank}(K, V) \leq s \Rightarrow\\{}\operatorname{finrank}(K, \operatorname{range}(\operatorname{finiteHankel}(A, B, C, r, s))) \leq \operatorname{finrank}(K, V') \land\\{}((k \mapsto \operatorname{markovParameter}(\operatorname{minimalDynamics}(A, B, C), \operatorname{minimalInput}(A, B, C), \operatorname{minimalOutput}(A, B, C), k)), \operatorname{finrank}(K, \operatorname{MinimalStateSpace}(A, B, C))) = ((k \mapsto \operatorname{markovParameter}(A, B, C, k)), \operatorname{finrank}(K, \operatorname{range}(\operatorname{finiteHankel}(A, B, C, r, s)))) \land\\{}\neg \operatorname{StateDimensionInvariantAt}((k \mapsto \operatorname{markovParameter}(A, B, C, k))) \land\\{}\operatorname{sInf}(\operatorname{sameBehaviorDimensions}(A, B, C)) = \operatorname{finrank}(K, \operatorname{range}(\operatorname{finiteHankel}(A, B, C, r, s))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HankelMinimalStateDimension.hankel_rank_lower_bound_and_quotient_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A, B, and C define a finite-dimensional discrete linear system. Assume the competing realization A', B', and C' has the same complete input-output behavior, expressed by equality of every Markov parameter.

For row and column horizons at least finrank(K,V), the common finite Hankel rank is no larger than finrank(K,V'). The named quotient realization (A_min, B_min, C_min) has every original Markov parameter and state dimension equal to that rank.

A one-dimensional padded realization witnesses that raw state dimension is not invariant under complete input-output behavior. The infimum of all finite same-behavior state dimensions is exactly the Hankel rank, and the named quotient realizes it.

## References

- Truth anchor: `D5/S3/Observer/Hankel/HankelMinimalStateDimension.hankel_rank_lower_bound_and_quotient_attainment`
- Dependency: [D5/S3/Observer/Hankel/HankelRankMinimality](HankelRankMinimality.md)
- Dependency: [D5/S3/Observer/Linear/ReachableObservableQuotientDescent](../Linear/ReachableObservableQuotientDescent.md)
