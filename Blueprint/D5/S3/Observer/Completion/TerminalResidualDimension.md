# Constant Stage Dimension with Zero Terminal Residual

## Abstract

The strict natural coordinate tails retain full dimension at every stage while their terminal intersection is zero.

**Theorem 1.1 (Full-sized coordinate tails have zero terminal intersection).**

$$\exists R: \mathbb{N} \to \operatorname{ClosedSubspace}\left(\operatorname{ell}\left(2, \mathbb{N}\right)\right), R_{0} = \operatorname{top}\left(\operatorname{ell}\left(2, \mathbb{N}\right)\right) \land\\(\forall n\in \mathbb{N}, \operatorname{StrictSubset}\left(R_{n + 1}, R_{n}\right)) \land\\(\forall n\in \mathbb{N}, \operatorname{LinearIsometric}\left(\mathbb{R}, R_{n}, \operatorname{ell}\left(2, \mathbb{N}\right)\right)) \land\\\operatorname{InfiniteDimensional}\left(\mathbb{R}, \operatorname{ell}\left(2, \mathbb{N}\right)\right) \land\\\operatorname{iInf}\left(R\right) = \operatorname{zeroSubspace}\left(\operatorname{ell}\left(2, \mathbb{N}\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/TerminalResidualDimension.constant_dimension_with_zero_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same closed coordinate-tail chain in the real Hilbert space of square-summable natural-numbered sequences as in the earlier residual-progress theorem.

Because the natural numbers contain no omega stage, the terminal is defined externally as the intersection of all natural stages. The transfinite residual theorem identifies this intersection with the residual after every basis coordinate is consumed.

The zeroth stage is the whole space, every successor inclusion is strict, and every stage is linearly isometric to the infinite-dimensional ambient space. Nevertheless, the terminal intersection is the zero subspace.

Empty and singleton index sets with a constant whole-space chain have nonzero intersection; constant zero chains have zero intersection. The theorem therefore makes no claim for arbitrary stage types.

## References

- Truth anchor: `D5/S3/Observer/Completion/TerminalResidualDimension.constant_dimension_with_zero_terminal`
- Dependency: [D5/S3/Observer/Completion/ResidualProgressMeasure](ResidualProgressMeasure.md)
