# Gaussian coefficient operator

## Abstract

A heterogeneous Gaussian coefficient operator from the actual joint Fock vector.

The Gaussian/Fock construction and factorial Bargmann/Fock normalization are classical, as described in FactorialFockMetric and InfiniteGaussianFock; AssessedProvenance.FromRepo identifies the repository Lean formalization and Mathlib reuse, not authorship of the classical construction or a literature novelty claim.

Let S and T be arbitrary mode types with decidable equality. The input D is InfiniteGaussianFock.Data on S plus T: an actual bounded complex-linear one-particle map L, holomorphically symmetric matrix K(i,j)=(L e(j))(i), 0<=q<1, norm(L)<=q, and a summable pair square series with total at most M. The completed Gaussian vector is the one constructed by InfiniteGaussianFock from common finite principal blocks. Columns and their summability are conclusions, not additional input certificates.

**Theorem 1.1 (Exact occupation splitting and normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.scale_join`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.scale_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-support sum equivalence splits an occupation on S plus T into a source occupation d and output occupation h. Its inverse joins them without losing zero or repeated occupations. The factorial weight of the join is weight(d)*weight(h), hence its real square-root scale is scale(d)*scale(h). Empty mode types still have the vacuum occupation.

**Theorem 1.2 (The whole matrix mass).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.matrix_square_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.matrix_square_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With output row h and source column d, c(h,d)=scale(d)*scale(h)*g(join(d,h)), where g is the actual holomorphic Gaussian coefficient of K. This equals the corresponding coordinate of D.vector. Reindexing its proved nonnegative summable square series by the occupation equivalence gives the exact whole matrix square sum norm(D.vector)^2. No conjugation of K or assumption about column normalization is used.

**Theorem 1.3 (Genuine square-summable output columns).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.column_square_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.column_square_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each fixed d gives a genuine output l2 vector column(d), by the nonnegative product-series criterion. Parseval and the product-series theorem identify the sum over all d of norm(column(d))^2 with norm(D.vector)^2. Each column also has an unconditional ON expansion in the output Hilbert norm.

**Theorem 1.4 (Same-space synthesis on the correct ambient sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.exists_block_operator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.exists_block_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient Hilbert space is l2(Occupation(S) plus Occupation(T)), distinct from l2(Occupation(S plus T)). Isometric coordinate inclusions Jsrc and Jout put each output column in the output block; all columns indexed by the extra output block are zero. Reindex the standard ON basis onto its range and apply HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns. The resulting endomorphism A has exactly these columns, is Hilbert-Schmidt, has their exact total square mass, and norm(A)<=sqrt(norm(D.vector)^2). The synthesis and its Cauchy-Schwarz suppliers retain the Apache-2.0 Physlib attribution in TraceClass.ColumnSynthesis and TraceClass.HilbertSchmidt.

**Theorem 1.5 (The actual heterogeneous map).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define C=Jout-adjoint composed with A composed with Jsrc, from the source factorial Fock Hilbert space to the generally different output space. Its action on each source ON vector is exactly column(d). Thus inner(e(h),C e(d))=scale(d)*scale(h)*g(join(d,h)), with the complex inner product conjugate-linear in its first argument.

**Theorem 1.6 (Exact zero extension).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_zero_extension`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_zero_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endomorphism Jout C Jsrc-adjoint equals A: it agrees on every source ON vector and vanishes on every output ON vector. This proves the Hilbert-Schmidt assertion in the existing same-space API, while C itself retains the genuine heterogeneous domain and codomain.

**Theorem 1.7 (Whole Hilbert-Schmidt square bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_square_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_square_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact sum over all source ON vectors of norm(C e(d))^2 equals norm(D.vector)^2, and is at most exp(M/(2*(1-q^2))). This includes the full occupation matrix and all mixed or repeated occupations.

**Theorem 1.8 (Operator norm bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Contractivity of the inclusions and their adjoints gives norm(C)<=sqrt(norm(D.vector)^2). The actual joint Gaussian bound therefore yields norm(C)<=exp(M/(4*(1-q^2))). The exponent is obtained by taking the square root of the whole square-mass bound.

**Theorem 1.9 (Exact factorial polynomial action).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite polynomial p, C(embedding(p)) is the finite sum over its support of (scale(d)*coeff(p,d)) times column(d). The embedding is the existing injective factorial Hilbert embedding, not an unweighted polynomial representation.

**Theorem 1.10 (Uniqueness and completed-input action).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_unique_on_polynomials`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_unique_on_polynomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous complex-linear map with that polynomial action equals C: normalized monomials give every ON vector, and finite-support vectors determine continuous maps. For every completed source input x, the unconditional Hilbert-norm sum of x(d) times column(d) equals C x.

**Theorem 1.11 (Two input legs and one output leg).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.triple_matrix_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.triple_matrix_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a kernel on (S plus T) plus U, both source occupations d and e belong to the domain; h is the sole output row. The ON entry is scale(d)*scale(e)*scale(h)*g(join(join(d,e),h)). A future tensor-to-matrix identification conjugates both domain coefficients. This convention never changes the holomorphic symmetry of K into Hermitian symmetry.

The construction does not identify C with the native field Y. The full normal-plus-Corr polynomial identity, Gram whitening, positive-frequency damping, same-term exponent regrouping, multi-field vacuum/source identities, and cycle, sewing and determinant realizations remain unproved here. No physical realization, full string theory, spacetime emergence or literature novelty follows from this analytic operator construction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_matrix`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_norm_le`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_polynomial`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_square_sum_le`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_unique_on_polynomials`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.coefficientOperator_zero_extension`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.column_square_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.exists_block_operator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.matrix_square_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.scale_join`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator.triple_matrix_coefficient`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis](../../Quantum/Analysis/TraceClass/ColumnSynthesis.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock](InfiniteGaussianFock.md)
