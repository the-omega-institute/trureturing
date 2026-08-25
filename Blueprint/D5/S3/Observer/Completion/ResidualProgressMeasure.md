# Residual Progress Measures

## Abstract

Strict Hilbert-space residual tails can retain full dimension while target-based projection residuals decrease stage by stage.

**Theorem 1.1 (A strict residual chain can retain the ambient dimension).**

$$\exists R: \mathbb{N} \to \operatorname{ClosedSubspace}\left(\operatorname{ell}\left(2, \mathbb{N}\right)\right), R_{0} = \operatorname{ell}\left(2, \mathbb{N}\right) \land\\(\forall n\in \mathbb{N}, \operatorname{StrictSubset}\left(R_{n + 1}, R_{n}\right)) \land \operatorname{Antitone}\left(R\right) \land\\(\forall n\in \mathbb{N}, \operatorname{LinearIsometric}\left(\mathbb{R}, R_{n}, \operatorname{ell}\left(2, \mathbb{N}\right)\right)) \land \operatorname{InfiniteDimensional}\left(\mathbb{R}, \operatorname{ell}\left(2, \mathbb{N}\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ResidualProgressMeasure.bare_dimension_not_progress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the real Hilbert space of square-summable natural-numbered sequences, let each stage be the closed coordinate tail.

The zeroth tail is the whole space and every successor inclusion is strict. Reindexing the remaining Hilbert basis gives a linear isometry from every tail to the ambient space.

The ambient carrier is also proved infinite-dimensional, so the unchanged Hilbert dimension cannot detect the strict descent.

**Theorem 1.2 (Target and test-family residual measures descend).**

$$\operatorname{Antitone}\left(R\right) \Rightarrow (\forall x, \operatorname{Antitone}\left(\left\lVert \operatorname{P}\left(R_{i}\right)(x) \right\rVert_{i}\right)) \land\\\operatorname{Antitone}\left(\operatorname{sup}_{x\in T} \left\lVert \operatorname{P}\left(R_{i}\right)(x) \right\rVert_{i}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ResidualProgressMeasure.target_residual_measures_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an antitone family of orthogonally complemented residual subspaces, projection through a later stage factors through projection at every earlier stage.

Projection contraction therefore makes each fixed-vector norm antitone. Taking a complete-lattice supremum in the extended nonnegative reals preserves that order for every test family.

The extended supremum also covers empty and unbounded test families. Kernel intersections are not included because no stagewise kernel order is specified by this norm-residual framework.

**Theorem 1.3 (Residual order is required for descent).**

$$\exists R: \operatorname{Bool}\left(\right) \to \operatorname{ClosedSubspace}\left(\mathbb{R}\right), \neg \operatorname{Antitone}\left(R\right) \land \neg \operatorname{Antitone}\left(\left\lVert \operatorname{P}\left(R_{i}\right)(1) \right\rVert_{i}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/ResidualProgressMeasure.antitone_residual_chain_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the two-element stage order, take the residual to move from the zero subspace to the whole real line.

This family is not antitone, and the projection norm of the target one increases from zero to one. Thus the residual-order hypothesis in the monotonicity theorem is necessary.

## References

- Truth anchor: `D5/S3/Observer/Completion/ResidualProgressMeasure.antitone_residual_chain_is_necessary`
- Truth anchor: `D5/S3/Observer/Completion/ResidualProgressMeasure.bare_dimension_not_progress`
- Truth anchor: `D5/S3/Observer/Completion/ResidualProgressMeasure.target_residual_measures_antitone`
- Dependency: [D5/S3/Quantum/Completion/TransfiniteBasisResidualTower](../../Quantum/Completion/TransfiniteBasisResidualTower.md)
