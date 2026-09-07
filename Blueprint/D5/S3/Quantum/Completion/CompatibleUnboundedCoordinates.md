# Compatible Unbounded Coordinates

## Abstract

Actual first-coordinate projections are compatible but the partial-one family is unbounded and unrealizable.

**Definition 1.1 (The actual first-coordinate span).**

$$\begin{gathered}\forall K: Type u, [\operatorname{RCLike}(K)],\\{}\forall n: \mathbb{N}, \operatorname{coordinateSpace}(K, n): \operatorname{Submodule}(K, \operatorname{lp}((i: \mathbb{N} \mapsto K), 2)) = \operatorname{span}(K, \operatorname{range}((i: \operatorname{Fin}(n) \mapsto \operatorname{single}(2, \operatorname{val}(i), 1)))).\end{gathered}$$

*Formalization.* `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinateSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates are numbered from zero. The range n consists of exactly the first n coordinates, and stage zero is the span of the empty set.

**Definition 1.2 (The actual partial-one vectors).**

$$\begin{gathered}\forall K: Type u, [\operatorname{RCLike}(K)],\\{}\forall n: \mathbb{N}, \operatorname{partialOnes}(K, n): \operatorname{lp}((i: \mathbb{N} \mapsto K), 2) = \sum_{i \in \operatorname{range}(n)} \operatorname{single}(2, i, 1).\end{gathered}$$

*Formalization.* `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.partialOnes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are finite sums in the existing lp space at exponent 2, with its existing norm and inner product.

**Proposition 1.3 (Finite-dimensional coordinate stages).**

$$\begin{gathered}\forall K: Type u, [\operatorname{RCLike}(K)],\\{}\forall n: \mathbb{N}, \operatorname{FiniteDimensional}(K, \operatorname{coordinateSpace}(K, n)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinateSpaceFiniteDimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite range of standard coordinate vectors spans each stage.

**Proposition 1.4 (Actual orthogonal projections).**

$$\begin{gathered}\forall K: Type u, [\operatorname{RCLike}(K)],\\{}\forall n: \mathbb{N}, \operatorname{HasOrthogonalProjection}(\operatorname{coordinateSpace}(K, n)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinateSpaceHasOrthogonalProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite dimensionality supplies completeness locally, so no stage-completeness hypothesis is added.

**Theorem 1.5 (Projection is coordinate truncation).**

$$\begin{gathered}\forall K: Type u, [\operatorname{RCLike}(K)],\\{}\forall n: \mathbb{N}, \forall x: \operatorname{lp}((i: \mathbb{N} \mapsto K), 2), \operatorname{starProjection}(\operatorname{coordinateSpace}(K, n), x) = \sum_{i \in \operatorname{range}(n)} \operatorname{single}(2, i, x(i)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinate_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite sum lies in the independently defined span. Its residual has zero first-n coordinates, so projection uniqueness applies. Mathlib's complex inner product is conjugate linear in the first argument; the proof uses the residual in that argument and the coordinate vector in the second.

**Theorem 1.6 (Compatible coordinates without a Hilbert-space realization).**

$$\begin{gathered}\forall K: Type u, [\operatorname{RCLike}(K)],\\{}(\operatorname{Monotone}((n: \mathbb{N} \mapsto \operatorname{coordinateSpace}(K, n)))) \land\\{}(\forall n: \mathbb{N}, \operatorname{partialOnes}(K, n) \in \operatorname{coordinateSpace}(K, n)) \land\\{}(\forall n: \mathbb{N}, \forall i: \mathbb{N}, \operatorname{partialOnes}(K, n)(i) = \operatorname{ite}(i < n, 1, 0)) \land\\{}(\forall m: \mathbb{N}, \forall n: \mathbb{N}, m \le n \implies \operatorname{starProjection}(\operatorname{coordinateSpace}(K, m), \operatorname{partialOnes}(K, n)) = \operatorname{partialOnes}(K, m)) \land\\{}(\forall n: \mathbb{N}, \Vert \operatorname{partialOnes}(K, n)\Vert^{2} = (n: \mathbb{R})) \land\\{}(\forall n: \mathbb{N}, \Vert \operatorname{partialOnes}(K, n)\Vert = \sqrt{n}) \land\\{}(\operatorname{Tendsto}((n: \mathbb{N} \mapsto \Vert \operatorname{partialOnes}(K, n)\Vert), \operatorname{atTop}(), \operatorname{atTop}())) \land\\{}(\neg\operatorname{BddAbove}(\operatorname{range}((n: \mathbb{N} \mapsto \Vert \operatorname{partialOnes}(K, n)\Vert)))) \land\\{}(\forall x: \operatorname{lp}((i: \mathbb{N} \mapsto K), 2), \forall n: \mathbb{N}, (\Vert \operatorname{starProjection}(\operatorname{coordinateSpace}(K, n), x)\Vert \le \Vert x\Vert \land \Vert \operatorname{starProjection}(\operatorname{coordinateSpace}(K, n), x)\Vert^{2} \le \Vert x\Vert^{2})) \land\\{}(\neg(\exists x: \operatorname{lp}((i: \mathbb{N} \mapsto K), 2), \forall n: \mathbb{N}, \operatorname{starProjection}(\operatorname{coordinateSpace}(K, n), x) = \operatorname{partialOnes}(K, n))) \land\\{}(\forall x: \operatorname{lp}((i: \mathbb{N} \mapsto K), 2), \operatorname{Summable}((i: \mathbb{N} \mapsto \Vert x(i)\Vert^{2}))) \land\\{}(\neg\operatorname{Summable}((i: \mathbb{N} \mapsto \Vert (1: K)\Vert^{2}))) \land\\{}(\neg\operatorname{Mem\ell p}((i: \mathbb{N} \mapsto (1: K)), 2)) \land\\{}(\neg(\exists z: \operatorname{boundedInverseLimit}((n: \mathbb{N} \mapsto \operatorname{coordinateSpace}(K, n))), \forall n: \mathbb{N}, (z: \operatorname{BoundedContinuousFunction}(\mathbb{N}, \operatorname{lp}((i: \mathbb{N} \mapsto K), 2)))(n) = \operatorname{partialOnes}(K, n))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.compatible_unbounded_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All earlier-stage projection equations hold, while the norms tend to infinity. Projection contraction excludes a common lp preimage. Actual lp vectors have summable squared coordinate norms, whereas constant-one coefficients do not. The final exclusion concerns the existing submodule of bounded functions; compatibility alone does not supply boundedness.

## References

- Truth anchor: `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.compatible_unbounded_coordinates`
- Truth anchor: `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinateSpace`
- Truth anchor: `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinateSpaceFiniteDimensional`
- Truth anchor: `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinateSpaceHasOrthogonalProjection`
- Truth anchor: `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.coordinate_projection`
- Truth anchor: `D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.partialOnes`
- Dependency: [D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction](BoundedInverseLimitReconstruction.md)
