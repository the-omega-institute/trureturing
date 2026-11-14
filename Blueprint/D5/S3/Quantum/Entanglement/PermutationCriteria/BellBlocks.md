# Finite Bell blocks from coordinate kernels

## Abstract

The four correlated half entries are separated by their row and column coordinate kernels.

**Theorem 1.1 (Independent isometries preserve the rectangular trace norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_two_isometries`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_two_isometries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a complex matrix with finite row and column index sets m and n. Let V have row set a and column set m, and W have row set b and column set n. If V* V and W* W are identity matrices, then the trace norm of V A W* equals the trace norm of A. Here star denotes the conjugate transpose, and the trace norm is Re Tr sqrt(A* A). This directly specializes the existing SicMubCorrelationTraceNormEquality.scaled_isometry_traceNorm at alpha=beta=1. The index sets need not have equal cardinalities, and empty index sets are included.

**Definition 1.2 (The matrix of a coordinate inclusion).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.coordinateEmbedding`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.coordinateEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an injection e from m to a, the coordinate inclusion matrix has entry one at row e(j) and column j, and entry zero elsewhere. It includes a vector in the larger coordinate space and sets every unused coordinate to zero.

**Theorem 1.3 (A coordinate inclusion is an isometry).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.coordinateEmbedding_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.coordinateEmbedding_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every injection e from m to a, the product of the conjugate transpose of its coordinate inclusion matrix with that matrix is the identity on m. Distinct columns have disjoint supports, and each column has exactly one entry equal to one. Combining two such inclusions with the rectangular isometry identity preserves the trace norm when an arbitrary finite matrix is included as a block with zero entries outside it.

**Theorem 1.4 (Independent bijective reindexing preserves the trace norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_submatrix_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_submatrix_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite rectangular complex matrix A, a bijection e onto its row index set and a bijection f onto its column index set satisfy traceNorm(A.submatrix e f)=traceNorm(A). The two changes of coordinates are independent. Their inverse coordinate inclusion matrices are isometries, so the rectangular two-isometry identity applies.

**Theorem 1.5 (Transpose preserves the trace norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every square complex matrix A on an arbitrary finite index set, traceNorm(A transpose)=traceNorm(A). This is the existing transpose invariance of unitarily invariant norms, transported along a finite indexing equivalence.

**Theorem 1.6 (Adjoint preserves the trace norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_conjTranspose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_conjTranspose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every square complex matrix A on an arbitrary finite index set, traceNorm(A*)=traceNorm(A). This is the existing adjoint invariance of unitarily invariant norms, transported along a finite indexing equivalence. In particular, the trace norms defined using A* A and A A* agree.

**Theorem 1.7 (Adjoint preserves the rectangular trace norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_conjTranspose_rect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_conjTranspose_rect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite rectangular complex matrix A, traceNorm(A*) equals traceNorm(A). Embed its row and column spaces into their disjoint sum, using independent coordinate isometries. The resulting square matrix and its adjoint have the same trace norm; the two-isometry identity then gives the rectangular equality. The row and column index sets may have different cardinalities.

**Theorem 1.8 (A constant singular value).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_of_scalar_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_of_scalar_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a rectangular complex matrix on finite index types, and let c be a nonnegative real number. If A-adjoint times A is c squared times the identity on the column index type, then traceNorm(A) equals c times the number of columns. The positive square root is c times the identity; zero c and empty index types are included.

**Definition 1.9 (The mixed witness column).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.mixedColumn`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.mixedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two-by-one matrix whose entries are both one half.

**Theorem 1.10 (The mixed column norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_mixedColumn`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_mixedColumn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace norm of mixedColumn is the positive square root of one half. Its one-by-one Gram matrix has entry one half.

**Definition 1.11 (Scalar identity blocks).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.halfIdentity`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.halfIdentity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number n, halfIdentity(n) is one half times the identity matrix on Fin n.

**Theorem 1.12 (Scalar identity block norms).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_halfIdentity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_halfIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, traceNorm(halfIdentity(n)) is n divided by two. In particular the split mixed witness block has norm one and the doubly crossed Bell block has norm two.

**Definition 1.13 (The Bell column).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellColumn`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four-by-one matrix whose entries are all one half.

**Theorem 1.14 (The Bell column norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellColumn`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellColumn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace norm of bellColumn is one. Its only Gram entry is one.

**Definition 1.15 (One crossed Bell equality).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellOneCross`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellOneCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row index is a pair of bits, the column index is a bit, and the entry is one half when the first row bit equals the column bit, and zero otherwise.

**Theorem 1.16 (The singly crossed Bell norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellOneCross`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellOneCross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace norm of bellOneCross is twice the positive square root of one half. Its Gram matrix is one half times the two-dimensional identity, so its two singular values are both the square root of one half.

**Definition 1.17 (The constant Bell square).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellSquare`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two-by-two matrix whose entries are all one half.

**Theorem 1.18 (The constant Bell square norm).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellSquare`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace norm of bellSquare is one. The matrix is positive semidefinite and its trace is one.

**Theorem 1.19 (Embedding one matrix unit).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.embedded_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.embedded_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite row and column types a,b,m,n with decidable equality, injections e from m to a and f from n to b, indices i in m and j in n, and a complex coefficient c, coordinateEmbedding(e) times single(i,j,c) times the adjoint of coordinateEmbedding(f) equals single(e(i),f(j),c). The sparse product has only the selected column and selected row. This identity is used to expand the embedded single-party and Bell density matrices.

**Theorem 1.20 (Trace norm of a Bell support pattern).**

$$\forall M:\operatorname{FiniteType}\left(\right), (\forall N:\operatorname{FiniteType}\left(\right), (\forall R:\operatorname{prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right) \to M, (\forall C:\operatorname{prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right) \to N, (\forall rk:\operatorname{Bool}\left(\right), (\forall rb:\operatorname{Bool}\left(\right), (\forall ck:\operatorname{Bool}\left(\right), (\forall cb:\operatorname{Bool}\left(\right), (((rk) \lor (ck)) \Rightarrow (((rb) \lor (cb)) \Rightarrow ((\operatorname{coordinateKernel}\left(R, rk, rb\right)) \Rightarrow ((\operatorname{coordinateKernel}\left(C, ck, cb\right)) \Rightarrow (\operatorname{traceNorm}\left(\operatorname{fourEntries}\left(R, C\right)\right) = \operatorname{bellValue}\left(\operatorname{indicator}\left((rk) \land (ck)\right) + \operatorname{indicator}\left((rb) \land (cb)\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_fourEntries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

fourEntries(R,C) is the sum, over the four pairs x in Fin 2 times Fin 2, of the matrix single(R(x),C(x),1/2). The finite row and column types have decidable equality. coordinateKernel(R,rk,rb) means that R(x)=R(y) if and only if rk being true forces equality of the first coordinates and rb being true forces equality of the second coordinates. The two Boolean flags for C have the same meaning. Each coordinate must occur in at least one side. indicator(b) is one for true and zero for false. Thus count is the number of coordinates that occur in both sides. The value bellValue is one at count zero, twice sqrt(1/2) at count one, and two at count two. Coordinate embeddings reduce the arbitrary finite row and column types to the retained coordinates. The nine possible nonempty routing patterns give the scalar identity, constant square, single-column, or singly crossed blocks.

**Theorem 1.21 (The three Bell norms are distinct).**

$$\operatorname{injectiveOn}\left(\operatorname{bellValue}\left(\right), \operatorname{closedNatInterval}\left(0, 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellValue_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three values are ordered as one, twice sqrt(1/2), and two. Equality of Bell norms therefore recovers the shared-coordinate count whenever both counts are at most two.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellColumn`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellOneCross`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellSquare`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.bellValue_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.coordinateEmbedding`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.coordinateEmbedding_isometry`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.embedded_single`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.halfIdentity`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.mixedColumn`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellColumn`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellOneCross`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_bellSquare`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_conjTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_conjTranspose_rect`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_fourEntries`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_halfIdentity`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_mixedColumn`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_of_scalar_gram`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_submatrix_equiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_transpose`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.traceNorm_two_isometries`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Schatten/TraceNorm](../../Schatten/TraceNorm.md)
- Dependency: [D5/S3/QuantumBounds/SicMubCorrelationTraceNormEquality](../../../QuantumBounds/SicMubCorrelationTraceNormEquality.md)
