# Joint Observer Visible Space and Residual

## Abstract

Joint effect families add visible directions and intersect invisible residuals.

**Theorem 1.1 (Joint observers add visibility and intersect residuals).**

$$\begin{aligned}\forall d: Nat, E1, E2: \operatorname{Set}\left(\operatorname{HermitianSpace}\left(d\right)\right),\\\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), \operatorname{union}\left(E1, E2\right)\right)\right) = \operatorname{join}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E1\right)\right), \operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E2\right)\right)\right) \land \\\operatorname{orthogonal}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), \operatorname{union}\left(E1, E2\right)\right)\right)\right) = \operatorname{meet}\left(\operatorname{orthogonal}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E1\right)\right)\right), \operatorname{orthogonal}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E2\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/JointObserverVisibleResidual.joint_observer_visible_and_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite matrix dimension d, each observer is represented by an arbitrary set of effects in the canonical real Hermitian space. Its visible space is the real span of the identity together with those effects.

The joint observer is constructed from the union of the two effect sets. Its visible space is the submodule join of the individual visible spaces, and its Hilbert--Schmidt orthogonal residual is the submodule meet of the individual residuals.

The proof applies the pinned library identities for the span of a set union and for the orthogonal complement of a submodule join.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/JointObserverVisibleResidual.joint_observer_visible_and_residual`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
