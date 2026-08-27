# Observation Rank Equality

## Abstract

A finite-dimensional readout and its two Gram compositions have the same rank.

**Theorem 1.1 (Readout, state Gramian, and observable Gramian have equal rank).**

$$\begin{gathered}\forall K, X, P: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(X)], [\operatorname{InnerProductSpace}(K, X)], [\operatorname{NormedAddCommGroup}(P)], [\operatorname{InnerProductSpace}(K, P)],\\{}[\operatorname{FiniteDimensional}(K, X)], [\operatorname{FiniteDimensional}(K, P)],\\{}M: \operatorname{LinearMap}(K, X, P) \Rightarrow\\{}finrank(K) \operatorname{range}(\operatorname{adjointComp}(M)) = finrank(K) \operatorname{range}(M) \land finrank(K) \operatorname{range}(M) = finrank(K) \operatorname{range}(\operatorname{compAdjoint}(M)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ObservationRankEquality.observation_rank_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source readout map is a linear map between finite-dimensional inner-product spaces. Its adjoint composition on the state space and the reverse composition on the readout space have ranges of the same finite rank as the readout itself.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/ObservationRankEquality.observation_rank_equality`
