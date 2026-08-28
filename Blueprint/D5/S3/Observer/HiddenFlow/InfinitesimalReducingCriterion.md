# Infinitesimal Reducing Criterion

## Abstract

Generator commutation, whole Hamiltonian-flow commutation, and complementary reduction are equivalent for finite complex matrices.

**Lemma 1.1 (Projection commutation is equivalent to reduction).**

$$\forall V, R, h: \operatorname{IsCompl}\left(V, R\right), T,\\{}T \operatorname{visibleProjectionMatrix}\left(V, R, h\right) = \operatorname{visibleProjectionMatrix}\left(V, R, h\right) T \iff \operatorname{IsReducing}\left(\operatorname{matrixToLinear}\left(T\right), V, R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion.commutes_visibleProjectionMatrix_iff_reducing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and R be complementary subspaces of a finite-dimensional complex coordinate space, and let P be the standard-basis matrix of the projection onto V along R. A matrix T commutes with P exactly when the linear operator represented by T preserves both V and R.

Writing the complementary projection as I minus P turns commutation into the vanishing of both cross blocks. Those two zero blocks are precisely the reducing condition for the decomposition V plus R.

**Theorem 1.2 (Generator commutation controls reduction along the whole flow).**

$$\begin{gathered}\forall n: \operatorname{Type}, [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(n\right)],\\{}V: \operatorname{Submodule}\left(\mathbb{C}, n \to \mathbb{C}\right), R: \operatorname{Submodule}\left(\mathbb{C}, n \to \mathbb{C}\right), h: \operatorname{IsCompl}\left(V, R\right), H: \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\\{}H \operatorname{visibleProjectionMatrix}\left(V, R, h\right) = \operatorname{visibleProjectionMatrix}\left(V, R, h\right) H \iff \\{}(\forall t: \mathbb{R}, \operatorname{hamiltonianPropagator}\left(H, t\right) \operatorname{visibleProjectionMatrix}\left(V, R, h\right) = \operatorname{visibleProjectionMatrix}\left(V, R, h\right) \operatorname{hamiltonianPropagator}\left(H, t\right)) \iff \\{}(\forall t: \mathbb{R}, \operatorname{IsReducing}\left(\operatorname{matrixToLinear}\left(\operatorname{hamiltonianPropagator}\left(H, t\right)\right), V, R\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion.infinitesimal_reducing_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the Hamiltonian flow U(t) = exp(-itH), three conditions are equivalent: H commutes with the visible projection matrix, every propagator U(t) commutes with that matrix, and the complementary subspaces reduce the linear operator represented by U(t) for every real time t.

Generator commutation passes to every exponential in the flow. Conversely, differentiating the flow commutation identity at time zero recovers commutation with the generator and hence with H after cancelling the nonzero scalar factor -i.

At each time, propagator commutation is equivalent to preservation of both complementary blocks by the preceding projection criterion. Thus the infinitesimal, global-flow, and flowwise-reducing descriptions carry the same information.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion.commutes_visibleProjectionMatrix_iff_reducing`
- Truth anchor: `D5/S3/Observer/HiddenFlow/InfinitesimalReducingCriterion.infinitesimal_reducing_criterion`
- Dependency: [D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria](VisibleHiddenProjectionCriteria.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../../Quantum/Dynamics/ProjectionProbabilityFlow.md)
