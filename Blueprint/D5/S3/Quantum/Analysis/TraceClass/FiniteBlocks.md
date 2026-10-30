# Positive trace-class blocks

## Abstract

Finite Hilbert sums preserve the full reference in each coordinate.

**Theorem 1.1 (Positive diagonal reference blocks).**

$$\forall H \in CompleteComplexHilbertSpace, I \in FiniteDecidableType, T \in \operatorname{End}\left(\operatorname{B}\left(I, H\right)\right), i \in I,\; 0 \le T \Rightarrow 0 \le \operatorname{compression}\left(T, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.compression_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is any complete complex Hilbert space, I is any finite type with decidable equality, and B(I,H) is PiLp 2 with one copy of H per coordinate. The coordinate pi_i is bounded evaluation and its adjoint iota_i inserts a vector in coordinate i. Compression is the actual operator pi_i T iota_i on H. Its quadratic form is the quadratic form of T evaluated on iota_i x, so positivity passes to the reference block.

**Theorem 1.2 (Trace-class compression to a different Hilbert space).**

$$\forall H \in CompleteComplexHilbertSpace, I \in FiniteDecidableType, T \in \operatorname{End}\left(\operatorname{B}\left(I, H\right)\right), i \in I,\; \left(\operatorname{IsTraceClass}\left(T\right) \land 0 \le T\right) \Rightarrow \operatorname{IsTraceClass}\left(\operatorname{compression}\left(T, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.compression_traceClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an arbitrary Hilbert basis b of H. The vectors iota_i(b_u), indexed by I times the entire index set of b, form a Hilbert basis of B(I,H): orthogonality is coordinatewise, and a vector orthogonal to every such vector has every coordinate zero. Reindexing this basis by its vector range permits the basis-independent trace-class criterion. The summable nonnegative diagonal of positive T restricts to each fixed coordinate. Since the absolute value of a positive operator equals itself, this restricted family proves that pi_i T iota_i is trace class. No countability, finite rank, finite reference dimension, or product-state hypothesis occurs.

**Theorem 1.3 (Finite splitting of the same joint trace).**

$$\forall H \in CompleteComplexHilbertSpace, I \in FiniteDecidableType, T \in \operatorname{End}\left(\operatorname{B}\left(I, H\right)\right),\; \left(\operatorname{IsTraceClass}\left(T\right) \land 0 \le T\right) \Rightarrow \operatorname{diagonalTraceSum}\left(T\right) = \operatorname{trace}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.trace_compression_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace on the block basis is the unconditional sum of the diagonal reference coefficients. Splitting its finite coordinate index gives sum_i Tr(pi_i T iota_i)=Tr(T). Every summand is computed from the same T; correlations in T are neither replaced nor independently chosen.

**Theorem 1.4 (Trace-class embedding into a fixed coordinate).**

$$\forall H \in CompleteComplexHilbertSpace, I \in FiniteDecidableType, A \in \operatorname{End}\left(H\right), i \in I,\; \left(\operatorname{IsTraceClass}\left(A\right) \land 0 \le A\right) \Rightarrow \operatorname{IsTraceClass}\left(\operatorname{embedding}\left(A, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.embedding_traceClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding is iota_i A pi_i. It is positive, and its diagonal on the block basis vanishes outside coordinate i. The remaining diagonal is exactly that of A. Its summability proves trace class in the full joint space.

**Theorem 1.5 (The fixed coordinate preserves positive trace and trace norm).**

$$\forall H \in CompleteComplexHilbertSpace, I \in FiniteDecidableType, A \in \operatorname{End}\left(H\right), i \in I,\; \left(\operatorname{IsTraceClass}\left(A\right) \land 0 \le A\right) \Rightarrow \left(\operatorname{trace}\left(\operatorname{embedding}\left(A, i\right)\right) = \operatorname{trace}\left(A\right) \land \operatorname{traceNorm}\left(\operatorname{embedding}\left(A, i\right)\right) = \operatorname{traceNorm}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.embedding_trace_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the embedding diagonal gives the unchanged complex trace. For positive trace-class operators the trace norm is the real trace, so the genuine trace norm is unchanged as well. In an absorbing output coordinate this is the isometric retention of the reference state.

**Theorem 1.6 (The tensor coordinates preserve the unchanged reference).**

$$\forall H \in CompleteComplexHilbertSpace, I \in FiniteDecidableType, u \in \operatorname{EuclideanSpace}\left(I\right), x \in H, i \in I,\; \operatorname{coordinate}\left(\operatorname{tensorCoordinates}\left(\operatorname{tensor}\left(u, x\right)\right), i\right) = \operatorname{smul}\left(\operatorname{coordinate}\left(u, i\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.tensorCoordinates_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

tensorCoordinates is a complex linear isometry equivalence from the Hilbert tensor product of the finite scalar system and H onto B(I,H). On a simple tensor u tensor x its i-th coordinate is u_i times x. The inner product is first checked on simple tensors and then on all tensors by the tensor induction principle. The underlying linear equivalence is onto; since the finite Hilbert sum is complete, this tensor product is already complete. Thus no restriction to simple tensors, finite-dimensional references, or separable references is imposed.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.compression_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.compression_traceClass`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.embedding_traceClass`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.embedding_trace_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.tensorCoordinates_tmul`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/FiniteBlocks.trace_compression_sum`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/LogRegularization](LogRegularization.md)
