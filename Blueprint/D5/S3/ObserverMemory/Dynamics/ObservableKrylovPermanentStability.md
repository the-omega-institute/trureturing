# Observable Krylov Permanent Stability

## Abstract

Equality of consecutive observable Krylov stages persists at every later stage.

**Theorem 1.1 (One stable observable Krylov step is permanently stable).**

$$\begin{gathered}\forall K, V, Y, T, C, m,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(V) \land \operatorname{InnerProductSpace}(K, V) \land \operatorname{FiniteDimensional}(K, V) \land\\{}\operatorname{NormedAddCommGroup}(Y) \land \operatorname{InnerProductSpace}(K, Y) \land \operatorname{FiniteDimensional}(K, Y) \land\\{}T \in \operatorname{LinearMap}(K, V, V) \land C \in \operatorname{LinearMap}(K, V, Y) \land m \in N \Rightarrow\\{}\operatorname{span}(K, \{{T^{*}}^{k}(C^{*}(y)) \mid 0 \le k \le m, y \in Y\}) = \operatorname{span}(K, \{{T^{*}}^{k}(C^{*}(y)) \mid 0 \le k \le m+1, y \in Y\}) \Rightarrow\\{}\forall r \in N, \operatorname{span}(K, \{{T^{*}}^{k}(C^{*}(y)) \mid 0 \le k \le m+r, y \in Y\}) = \operatorname{span}(K, \{{T^{*}}^{k}(C^{*}(y)) \mid 0 \le k \le m, y \in Y\}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/ObservableKrylovPermanentStability.observable_krylov_once_stable_permanently` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state and output carriers are finite-dimensional inner-product spaces over a real or complex scalar field. The evolution and readout are arbitrary linear maps on those carriers.

Each displayed tower stage is the span of the adjoint evolution orbit of the adjoint readout range through the stated depth. Thus the observable object is constructed before stability is asserted.

Equality of stages m and m plus one makes stage m invariant under the adjoint evolution. Every later generator remains in that stage, while monotonicity supplies the reverse inclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/ObservableKrylovPermanentStability.observable_krylov_once_stable_permanently`
- Dependency: [D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound](ObservableKrylovGrowthBound.md)
