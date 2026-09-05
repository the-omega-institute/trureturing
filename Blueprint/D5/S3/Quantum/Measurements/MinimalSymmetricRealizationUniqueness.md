# Minimal Symmetric Realization Uniqueness

## Abstract

Equal moments determine a minimal symmetric real realization up to an orthogonal intertwiner.

**Theorem 1.1 (Orthogonal equivalence of minimal symmetric realizations).**

$$\begin{aligned}\forall U: \operatorname{Type}\left(\right), E: \operatorname{Type}\left(\right), W: \operatorname{Type}\left(\right),\\{}[\operatorname{NormedAddCommGroup}\left(U\right), \operatorname{InnerProductSpace}\left(\mathbb{R}, U\right), \operatorname{FiniteDimensional}\left(\mathbb{R}, U\right)],\\{}[\operatorname{NormedAddCommGroup}\left(E\right), \operatorname{InnerProductSpace}\left(\mathbb{R}, E\right), \operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)],\\{}[\operatorname{NormedAddCommGroup}\left(W\right), \operatorname{InnerProductSpace}\left(\mathbb{R}, W\right), \operatorname{FiniteDimensional}\left(\mathbb{R}, W\right)],\\\forall A: \operatorname{LinearMap}\left(\mathbb{R}, E, E\right), \widetilde{A}: \operatorname{LinearMap}\left(\mathbb{R}, W, W\right),\\B: \operatorname{LinearMap}\left(\mathbb{R}, U, E\right), \widetilde{B}: \operatorname{LinearMap}\left(\mathbb{R}, U, W\right),\\(\operatorname{IsSymmetric}\left(A\right)) \implies \\(\operatorname{IsSymmetric}\left(\widetilde{A}\right)) \implies \\(\forall k: \mathbb{N}, \operatorname{comp}\left(\operatorname{adjoint}\left(B\right), \operatorname{comp}\left(A^{k}, B\right)\right) = \operatorname{comp}\left(\operatorname{adjoint}\left(\widetilde{B}\right), \operatorname{comp}\left(\widetilde{A}^{k}, \widetilde{B}\right)\right)) \implies \\(\operatorname{reachableSubspace}\left(A, B\right) = \operatorname{top}\left(\right)) \implies \\(\operatorname{reachableSubspace}\left(\widetilde{A}, \widetilde{B}\right) = \operatorname{top}\left(\right)) \implies \\\exists Q: \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, E, W\right),\\(\operatorname{comp}\left(\operatorname{toLinearMap}\left(Q\right), A\right) = \operatorname{comp}\left(\widetilde{A}, \operatorname{toLinearMap}\left(Q\right)\right)) \land (\operatorname{comp}\left(\operatorname{toLinearMap}\left(Q\right), B\right) = \widetilde{B})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness.minimal_symmetric_realization_uniqueness` (`✓ std3`). ∎

*Citation.* Jan C. Willems (1976). *Realization of systems with internal passivity and symmetry constraints*. DOI: [10.1016/0016-0032(76)90081-8](https://doi.org/10.1016/0016-0032(76)90081-8).

*Commentary.*

The spaces U, E, and W are arbitrary finite-dimensional real inner-product spaces. W represents the second state space. LinearMap denotes a real linear map, adjoint is the inner-product adjoint, and comp is composition. In orthonormal coordinates the adjoint is the transpose in the source formula.

IsSymmetric is imposed on both dynamics: the inner product of A x with y equals that of x with A y, and likewise for the second dynamics. The two reachableSubspace hypotheses use the frozen repository definition displayed below, with all nonnegative powers and all input vectors. LinearIsometryEquiv is a surjective linear inner-product isometry; toLinearMap retains its underlying linear map.

$$
\begin{aligned}\forall U: \operatorname{Type}\left(\right), E: \operatorname{Type}\left(\right),\\{}[\operatorname{NormedAddCommGroup}\left(U\right), \operatorname{InnerProductSpace}\left(\mathbb{R}, U\right), \operatorname{FiniteDimensional}\left(\mathbb{R}, U\right)],\\{}[\operatorname{NormedAddCommGroup}\left(E\right), \operatorname{InnerProductSpace}\left(\mathbb{R}, E\right), \operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)],\\\forall A: \operatorname{LinearMap}\left(\mathbb{R}, E, E\right), B: \operatorname{LinearMap}\left(\mathbb{R}, U, E\right),\\\operatorname{reachableSubspace}\left(A, B\right) = \operatorname{span}\left(\mathbb{R}, \{x: E \mid \exists k: \mathbb{N}, v: U, x = \left(A^{k}\right)\left(B\left(v\right)\right)\}\right)\end{aligned}
$$

The proof sends each finite sum of iterated inputs to the same sum in the second realization. Symmetry and moment equality yield equality of the two Gram forms, hence equality of their kernels. The map descends through the quotient; minimality gives surjectivity on both sides. Increasing the generator power gives the dynamics identity, and power zero gives the input identity.

The literature attribution concerns minimal internally symmetric realizations and their invariant quadratic form. This formalization proves the real positive-metric case directly from moments.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness.minimal_symmetric_realization_uniqueness`
- Dependency: [D5/S3/Observer/LinearMemory/ReachableObservableQuotientReachability](../../Observer/LinearMemory/ReachableObservableQuotientReachability.md)
