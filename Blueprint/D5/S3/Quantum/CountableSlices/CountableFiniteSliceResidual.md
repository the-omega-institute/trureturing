# Countable Finite-Slice Residual

## Abstract

Countably many finite Hilbert slices generate only a separable cumulative space.

**Theorem 1.1 (Finite countable slicing leaves a residual in nonseparable space).**

$$\forall k: \operatorname{RCLikeField}(),\ \forall H: \operatorname{CompleteHilbertSpace}(k),\ \forall S_{0}, E,\ \operatorname{FiniteDimensional}(S_{0}) \land (\forall n\in \mathbb{N}, \operatorname{FiniteDimensional}(E_{n+1})) \land (\forall n\in \mathbb{N}, S_{n} = S_{0} \operatorname{orthogonalSum} \operatorname{finiteSliceSum}(E, n) \land E_{n+1} \subseteq \operatorname{OrthogonalComplement}(S_{n})) \Rightarrow S_{\infty} = \operatorname{ClosureUnion}(S) \land R_{\infty} = \operatorname{OrthogonalComplement}(S_{\infty}) \land \operatorname{SeparableSpace}(S_{\infty}) \land (\neg\operatorname{SeparableSpace}(H) \Rightarrow R_{\infty} \neq \{0\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CountableSlices/CountableFiniteSliceResidual.countable_finite_slice_separable_and_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complete real or complex Hilbert space. Starting from a finite-dimensional subspace S0, stage n is constructed from S0 and the first n finite-dimensional slices. Each next slice is required to lie in the orthogonal residual of the prior stage.

A finite basis makes every stage a separable subset. The countable union of the stages remains separable, as do its linear span and closure. This closure is the completion family's canonical cumulativeSpace.

The canonical residualSpace is the cumulative orthogonal complement. If that residual were zero, Mathlib's orthogonal_eq_bot_iff would make the cumulative space all of H, contradicting nonseparability.

The completion family's existing cumulativeSpace and residualSpace are imported as the single source of truth. Pinned Mathlib has no exact combined theorem; the proof applies its countable-union, span, closure, subtype-separability, and orthogonal-complement results.

The full one-dimensional initial stage and zero slice family over the real line compiles as a simultaneous witness for the carrier, recursion premise, and both public conclusions.

## References

- Truth anchor: `D5/S3/Quantum/CountableSlices/CountableFiniteSliceResidual.countable_finite_slice_separable_and_residual`
- Dependency: [D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction](../Completion/BoundedInverseLimitReconstruction.md)
