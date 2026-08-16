# No Unitary-Natural Orthogonal Selector

## Abstract

No unit choice on finite subspaces is natural under every unitary symmetry.

**Theorem 1.1 (There is no unitary-natural orthogonal selector).**

$$\forall k, H: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{InnerProductSpace}_{k}(H)],\ \neg\operatorname{FiniteDimensional}_{k}(H) \Rightarrow \neg\exists eta: \operatorname{FiniteSubspace}\left(k, H\right) \to H,\ (\forall M \in \operatorname{FiniteSubspace}\left(k, H\right),\ \operatorname{select}\left(eta, M\right) \in M^{\perp} \land \operatorname{norm}\left(\operatorname{select}\left(eta, M\right)\right) = 1) \land (\forall U \in \operatorname{Unitary}\left(H\right), M \in \operatorname{FiniteSubspace}\left(k, H\right),\ \operatorname{select}\left(eta, \operatorname{map}\left(U, M\right)\right) = \operatorname{map}\left(U, \operatorname{select}\left(eta, M\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitaryNaturalSelector.no_unitary_natural_orthogonal_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be an infinite-dimensional real or complex inner-product space. There is no rule assigning every finite-dimensional subspace M a unit vector in its orthogonal complement while commuting with every surjective linear isometry of H.

Apply naturality at the zero subspace to the negative identity isometry. The zero subspace is finite-dimensional and fixed by negation, so the selected vector must equal its own negative. Scalar cancellation makes it zero, contradicting its prescribed norm one. The proof does not use completeness, so the formal result is stronger than the Hilbert-space source statement.

This does not contradict the existing FiniteLayerProjectionEscape theorem, which supplies a unit vector separately whenever an orthogonal residual is nonzero. The obstruction is the demand that all choices be natural under every unitary symmetry.

Repository and pinned-Mathlib searches found no theorem for the full no-go statement. Loogle supplied LinearIsometryEquiv.neg, the finite-dimensional zero-subspace instance, and preservation of finite dimensionality under Submodule.map. The attempted LeanSearch API request returned HTTP 404 and is not counted as a negative hit.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/UnitaryNaturalSelector.no_unitary_natural_orthogonal_selector`
