# Dense-Tower Strong Completion

## Abstract

A dense increasing Hilbert-subspace tower converges strongly to identity.

**Theorem 1.1 (Dense-tower projections converge strongly).**

$$\begin{aligned}\forall K, H, A, \operatorname{Hilbert}\left(K, H\right), \operatorname{Nonempty}\left(A\right),\\S: A \to \operatorname{ClosedSubspace}\left(H\right), \operatorname{Monotone}\left(S\right),\\\overline{\operatorname{iSup}\left(a, S(a)\right)} = H \Rightarrow\\(\forall x\in H, \operatorname{lim}\left(a, \infty, \operatorname{P}\left(S(a)\right)(x)\right) = x) \land\\(\forall x\in H, \operatorname{lim}\left(a, \infty, \left\lVert {I - \operatorname{P}\left(S(a)\right)}(x) \right\rVert\right) = 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/DenseTowerStrongCompletion.dense_tower_strong_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a nonempty directed increasing tower of closed projection subspaces in a Hilbert space. Its closed supremum is assumed to be the whole ambient space.

For every fixed vector, the canonical orthogonal projections onto the stages converge in norm to that vector.

Subtracting the projection limit from the constant identity vector and applying continuity of the norm gives the equivalent identity-minus-projection residual convergence to zero.

## References

- Truth anchor: `D5/S3/Quantum/Completion/DenseTowerStrongCompletion.dense_tower_strong_completion`
