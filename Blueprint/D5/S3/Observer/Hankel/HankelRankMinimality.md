# Hankel Rank Minimality

## Abstract

Once both finite horizons reach the state-space dimension, the block Hankel rank is the reachable dimension minus the invisible reachable dimension.

**Theorem 1.1 (Stable Hankel rank counts visible reachable directions).**

$$\begin{gathered}\forall K, V, U, Y: Type,\\{}\operatorname{Field}(K) \land \operatorname{AddCommGroup}(V) \land \operatorname{Module}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{AddCommGroup}(U) \land \operatorname{Module}(K, U) \land \operatorname{AddCommGroup}(Y) \land \operatorname{Module}(K, Y) \land\\{}A \in \operatorname{LinearMap}(K, V, V) \land B \in \operatorname{LinearMap}(K, U, V) \land C \in \operatorname{LinearMap}(K, V, Y) \land\\{}r, s \in N, \operatorname{finrank}(K, V) \leq r \land \operatorname{finrank}(K, V) \leq s \Rightarrow\\{}\operatorname{finrank}(K, \operatorname{range}(\operatorname{finiteHankel}(A, B, C, r, s))) = \operatorname{finrank}(K, \operatorname{reachableSubspace}(A, B)) - \operatorname{finrank}(K, \operatorname{inf}(\operatorname{reachableSubspace}(A, B), \operatorname{eventualKernel}(C, A))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/HankelRankMinimality.hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be the state evolution, B the input map, and C the readout of a finite-dimensional linear system over a field. The finite Hankel map has block (i,j) equal to C A^(i+j) B.

For row and column horizons at least finrank(K,V), its range has dimension equal to the imported reachable subspace dimension minus the dimension of its intersection with the imported all-future kernel.

## References

- Truth anchor: `D5/S3/Observer/Hankel/HankelRankMinimality.hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim`
- Dependency: [D5/S3/Observer/LinearMemory/ReachableObservableQuotientReachability](../LinearMemory/ReachableObservableQuotientReachability.md)
