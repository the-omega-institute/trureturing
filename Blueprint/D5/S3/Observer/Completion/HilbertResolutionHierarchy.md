# Hilbert Resolution Hierarchy

## Abstract

Uniform Hilbert resolution controls state-family and member-target residuals, while proper projection stages obstruct uniform resolution.

**Theorem 1.1 (Uniform resolution implies family and target resolution).**

$$\begin{gathered}\forall K, H: Type,\\{}\operatorname{RCLike}\left(K\right) \land \operatorname{NormedAddCommGroup}\left(H\right) \land \operatorname{InnerProductSpace}\left(K, H\right),\\{}V: \mathbb{N} \to \operatorname{Submodule}\left(K, H\right), (\forall n\in \mathbb{N}, \operatorname{HasOrthogonalProjection}\left(V(n)\right)),\\{}T: \operatorname{Set}\left(H\right), x: H,\\{}(\operatorname{lim}\left(n, \infty, \left\lVert I - \operatorname{P}\left(V(n)\right) \right\rVert\right) = 0 \Rightarrow \operatorname{lim}\left(n, \infty, \operatorname{sup}_{y\in T} \left\lVert \operatorname{P}\left(V(n)^{\perp}\right)(y) \right\rVert\right) = 0) \land\\{}(x\in T \Rightarrow \operatorname{lim}\left(n, \infty, \operatorname{sup}_{y\in T} \left\lVert \operatorname{P}\left(V(n)^{\perp}\right)(y) \right\rVert\right) = 0 \Rightarrow \operatorname{lim}\left(n, \infty, \left\lVert \operatorname{P}\left(V(n)^{\perp}\right)(x) \right\rVert\right) = 0) \land\\{}((\forall n\in \mathbb{N}, V(n) \neq top) \Rightarrow ((\forall n\in \mathbb{N}, \left\lVert I - \operatorname{P}\left(V(n)\right) \right\rVert = 1) \land \neg \operatorname{lim}\left(n, \infty, \left\lVert I - \operatorname{P}\left(V(n)\right) \right\rVert\right) = 0)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/HilbertResolutionHierarchy.hilbert_resolution_hierarchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary orthogonally complemented Hilbert subspaces V(n), the residual is the canonical orthogonal complement V(n)-perp. The family residual is the extended nonnegative supremum of its projection norms, so empty and unbounded families remain defined.

Operator-norm convergence to the identity forces the visible stage to be the whole space eventually, since every proper stage remains exactly one unit away. The family residual is then eventually zero.

A member target is bounded by the same family's supremum. Finally, the frozen uniform-completion obstruction supplies both the norm-one identity and nonconvergence when every stage is proper.

## References

- Truth anchor: `D5/S3/Observer/Completion/HilbertResolutionHierarchy.hilbert_resolution_hierarchy`
- Dependency: [D5/S3/Observer/Completion/ResidualProgressMeasure](ResidualProgressMeasure.md)
- Dependency: [D5/S3/Quantum/Completion/UniformCompletionObstruction](../../Quantum/Completion/UniformCompletionObstruction.md)
