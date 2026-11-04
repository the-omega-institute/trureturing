# Upper norm compression reduces to three block columns

## Abstract

For every real p at least two, a finite family of compatible complex block columns admits nonnegative square-root weights supported on at most three original columns. The compression Gram matrix is unchanged and the Schatten p-norm does not decrease. Therefore the upper norm-compression inequality for one, two and three columns implies it for every finite number of columns.

**Lemma 1.1 (Expansion in an orthonormal eigenbasis).**

$$\forall (E : Type), [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)], [\operatorname{FiniteDimensional}\left(\mathbb{C}, E\right)], \forall (T : \operatorname{LinearMap}\left(\mathbb{C}, E, E\right)), \forall (n : \mathbb{N}), \forall (hn : \operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, E\right) = n), \forall (hT : \operatorname{LinearMap}.\operatorname{IsSymmetric}\left(T\right)), \forall (x : E), \operatorname{Complex}.\operatorname{re}\left(\operatorname{inner}\left(\mathbb{C}, x, T\left(x\right)\right)\right) = \sum_{j : \operatorname{Fin}\left(n\right)} \left\lVert \operatorname{inner}\left(\mathbb{C}, \operatorname{LinearMap}.\operatorname{IsSymmetric}.\operatorname{eigenvectorBasis}\left(hT, hn, j\right), x\right) \right\rVert^{2} \cdot \operatorname{LinearMap}.\operatorname{IsSymmetric}.\operatorname{eigenvalues}\left(hT, hn, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.expectation_eq_eigenvalue_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real quadratic expectation is the eigenvalue-weighted sum of squared eigenvector coordinates.

**Theorem 1.2 (Diagonal power sums are bounded by spectral power sums).**

$$\forall (E : Type), [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)], [\operatorname{FiniteDimensional}\left(\mathbb{C}, E\right)], \forall (T : \operatorname{LinearMap}\left(\mathbb{C}, E, E\right)), \forall (n : \mathbb{N}), \forall (hn : \operatorname{Module}.\operatorname{finrank}\left(\mathbb{C}, E\right) = n), \forall (hT : \operatorname{LinearMap}.\operatorname{IsPositive}\left(T\right)), \forall (b : \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, E\right)), \forall (q : \mathbb{R}), (1 \le q) \Rightarrow (\sum_{i : \operatorname{Fin}\left(n\right)} \operatorname{Complex}.\operatorname{re}\left(\operatorname{inner}\left(\mathbb{C}, b\left(i\right), T\left(b\left(i\right)\right)\right)\right)^{q} \le \sum_{j : \operatorname{Fin}\left(n\right)} \operatorname{LinearMap}.\operatorname{IsSymmetric}.\operatorname{eigenvalues}\left(\operatorname{LinearMap}.\operatorname{IsPositive}.\operatorname{isSymmetric}\left(hT\right), hn, j\right)^{q})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.diagonal_power_le_eigenvalue_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive linear map and q at least one, Jensen's inequality in each orthonormal coordinate bounds the diagonal power sum by the eigenvalue power sum.

**Lemma 1.3 (Singular powers from the column Gram matrix).**

$$\forall (m : Type), \forall (n : Type), [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(m\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (p : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), (0 < p) \Rightarrow (\operatorname{schattenPow}\left(p, A\right) = \sum_{i : n} \operatorname{Matrix}.\operatorname{IsHermitian}.\operatorname{eigenvalues}\left(\operatorname{Matrix}.\operatorname{{{{isHermitian}_{conjTranspose}}_{mul}}_{self}}\left(A\right), i\right)^{\frac{p}{2}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_columnGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p positive, the Schatten power sum is the p/2 power sum of the eigenvalues of the column Gram matrix.

**Lemma 1.4 (Schatten power sums are nonnegative).**

$$\forall (m : Type), \forall (n : Type), [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(m\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (p : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), 0 \le \operatorname{schattenPow}\left(p, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every singular-value power is nonnegative, hence so is their finite sum.

**Lemma 1.5 (Schatten norms are nonnegative).**

$$\forall (m : Type), \forall (n : Type), [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(m\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (p : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), 0 \le \operatorname{schattenNorm}\left(p, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real power of a nonnegative power sum is nonnegative.

**Lemma 1.6 (The positive exponent recovers the power sum).**

$$\forall (n : Type), [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (q : \mathbb{R}), (0 < q) \Rightarrow (\forall (A : \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), \operatorname{schattenNorm}\left(q, A\right)^{q} = \operatorname{schattenPow}\left(q, A\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q positive, raising the Schatten norm to q returns its singular-value power sum.

**Definition 1.7 (Hermitian eigenvalue power sum).**

Lean statement: `D5/S3/Quantum/NormCompression/UpperBranchReduction.eigenPow`

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.eigenPow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing eigenvalue power sum is public so the actual finite power trace supplier can reuse its exact Schatten and Gram identification.

**Lemma 1.8 (Actual row Gram spectrum).**

Lean statement: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_rowGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_rowGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real exponent and arbitrary finite rectangular complex matrix, the Schatten power equals the power sum over the actual row Gram spectrum. This is the existing proof exposed for reuse.

**Lemma 1.9 (Row Gram eigenvalue power sum).**

Lean statement: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_eigenPow_rowGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_eigenPow_rowGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact existing Schatten power and row Gram eigenvalue identity is exposed without changing its proof.

**Lemma 1.10 (PSD Schatten and eigenvalue powers).**

Lean statement: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_eigenPow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_eigenPow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive semidefinite square matrix and a positive real exponent, the Schatten and eigenvalue power sums agree. The finite power trace continuity proof consumes this exact existing identity.

**Lemma 1.11 (Nonnegative scaling of Schatten powers).**

Lean statement: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_sqrt_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_sqrt_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative real w and positive p, multiplying a finite rectangular complex matrix by sqrt(w) multiplies its Schatten power by w^(p/2), including w = 0. The finite power degree one homogeneity proof consumes this existing identity.

**Definition 1.12 (Singular-value power sum).**

$$\forall (m : Type), \forall (n : Type), [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(m\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (p : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), \operatorname{schattenPow}\left(p, A\right) = \sum_{i \in \operatorname{Finsupp}.\operatorname{support}\left(\operatorname{LinearMap}.\operatorname{singularValues}\left(\operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A\right)\right)\right)} \operatorname{LinearMap}.\operatorname{singularValues}\left(\operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A\right)\right)\left(i\right)^{p}$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2 defines the Schatten norm by ‖A‖_p = (Tr(|A|^p))^(1/p). The finite trace power is the sum of powers of LinearMap.singularValues of Matrix.toEuclideanLin A. Only nonzero singular values occur in its Finsupp.support; at the exponents used below, omitted zero values contribute zero.

**Definition 1.13 (Schatten norm).**

$$\forall (m : Type), \forall (n : Type), [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(m\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (p : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), \operatorname{schattenNorm}\left(p, A\right) = \operatorname{schattenPow}\left(p, A\right)^{\frac{1}{p}}$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2, verbatim: "For a general matrix or operator A, they are defined as" followed by ‖A‖_p = (Tr(|A|^p))^(1/p). Real.rpow is used for both powers, and 1/p is real division. The reduction only uses p >= 2, so neither p = 0 nor the infinite-exponent norm is involved.

**Definition 1.14 (Compatible block-column concatenation).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), \forall (C : (J \to Type)), \forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \forall (i : \operatorname{Sum}\left(HA, HB\right)), \forall (jk : \operatorname{Sigma}\left(C\right)), \operatorname{assemble}\left(A, B\right)\left(i, jk\right) = \operatorname{Matrix}.\operatorname{fromRows}\left(A\left(\operatorname{Sigma}.\operatorname{fst}\left(jk\right)\right), B\left(\operatorname{Sigma}.\operatorname{fst}\left(jk\right)\right)\right)\left(i, \operatorname{Sigma}.\operatorname{snd}\left(jk\right)\right)$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.assemble` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2 writes T as the two block rows (A_1,...,A_N) and (B_1,...,B_N). J indexes the columns, HA and HB index the row spaces, and C j is the column space shared by A j and B j. Sigma C concatenates these column spaces, which may have different finite dimensions. Matrix.fromRows stacks the two blocks.

**Definition 1.15 (Square-root column rescaling).**

$$\forall (m : Type), \forall (n : Type), \forall (w : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), \operatorname{rescale}\left(w, A\right) = (\operatorname{Real}.\operatorname{sqrt}\left(w\right) : \mathbb{C}) \cdot A$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both blocks of column j are multiplied by the same nonnegative square root. The displayed coercion casts the real scalar to Complex. In the reduction, w j >= 0, including zero weights.

**Definition 1.16 (The two-row norm compression).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), \forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(2\right)), \forall (j : J), \operatorname{compression}\left(p, A, B\right)\left(i, j\right) = ((if (i = 0) then \operatorname{schattenNorm}\left(p, A\left(j\right)\right) else \operatorname{schattenNorm}\left(p, B\left(j\right)\right)) : \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.compression` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2, verbatim: "I denote by 𝒞ₚ(T) its Schatten p-norm compression," followed by the two scalar rows (‖A_1‖_p,...,‖A_N‖_p) and (‖B_1‖_p,...,‖B_N‖_p). Row i = 0 is the A row; the other element of Fin 2 is the B row. Each nonnegative real entry is cast to Complex.

**Definition 1.17 (Compression Gram matrix).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(J\right)], [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), \forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \operatorname{compressionGram}\left(p, A, B\right) = \operatorname{compression}\left(p, A, B\right) \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{compression}\left(p, A, B\right)\right)$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.compressionGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The compression Gram matrix uses Matrix.conjTranspose and lives on the fixed row type Fin 2. Its entries are the sums of the squared top norms, squared bottom norms and products of the two norms.

**Theorem 1.18 (Three active weights preserve the compression Gram matrix).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(J\right)], [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(J\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), (2 \le p) \Rightarrow (\forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \exists (w : (J \to \mathbb{R})), (\forall (j : J), 0 \le w\left(j\right)) \land ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)\right) \le 3) \land ((\operatorname{compressionGram}\left(p, (fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), A\left(j\right)\right)), (fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), B\left(j\right)\right))\right) = \operatorname{compressionGram}\left(p, A, B\right)) \land (\operatorname{schattenNorm}\left(p, \operatorname{assemble}\left(A, B\right)\right) \le \operatorname{schattenNorm}\left(p, \operatorname{assemble}\left((fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), A\left(j\right)\right)), (fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), B\left(j\right)\right))\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescaling_upper_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three real moments are (‖A_j‖_p^2, ‖B_j‖_p^2, ‖A_j‖_p ‖B_j‖_p). A signed dependence among more than three active moment vectors gives two nonnegative boundary weights whose convex combination is the original weight. One boundary has no smaller convex Schatten power. Repeating the face move terminates with at most three active weights. Columns with both blocks zero are discarded before the face moves.

**Theorem 1.19 (At most three actual block columns).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(J\right)], [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(J\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), (2 \le p) \Rightarrow (\forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \exists (w : (J \to \mathbb{R})), (\forall (j : J), 0 \le w\left(j\right)) \land ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)\right) \le 3) \land ((\operatorname{compressionGram}\left(p, (fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), A\left(\operatorname{val}\left(j\right)\right)\right)), (fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), B\left(\operatorname{val}\left(j\right)\right)\right))\right) = \operatorname{compressionGram}\left(p, A, B\right)) \land (\operatorname{schattenNorm}\left(p, \operatorname{assemble}\left(A, B\right)\right) \le \operatorname{schattenNorm}\left(p, \operatorname{assemble}\left((fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), A\left(\operatorname{val}\left(j\right)\right)\right)), (fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), B\left(\operatorname{val}\left(j\right)\right)\right))\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.upper_three_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting to the finite support of w deletes every zero-weight column. The selected index is a subtype member, and val returns its original column index. The compression Gram matrix is exactly the original one, and the Schatten norm of the selected, rescaled block matrix is at least the original norm. The row dimensions and the individual column dimensions are unrestricted finite types.

**Theorem 1.20 (The three-column case implies the upper branch).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(J\right)], [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(J\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), (2 \le p) \Rightarrow ((\forall (K : Type), [\operatorname{Fintype}\left(K\right)], [\operatorname{DecidableEq}\left(K\right)], \forall (D : (K \to Type)), [\forall (k : K), \operatorname{Fintype}\left(D\left(k\right)\right)], [\forall (k : K), \operatorname{DecidableEq}\left(D\left(k\right)\right)], \forall (Ap : \forall (j : K), \operatorname{Matrix}\left(HA, D\left(j\right), \mathbb{C}\right)), \forall (Bp : \forall (j : K), \operatorname{Matrix}\left(HB, D\left(j\right), \mathbb{C}\right)), (0 < \operatorname{Fintype}.\operatorname{card}\left(K\right)) \Rightarrow ((\operatorname{Fintype}.\operatorname{card}\left(K\right) \le 3) \Rightarrow (\operatorname{schattenNorm}\left(p, \operatorname{assemble}\left(Ap, Bp\right)\right) \le \operatorname{schattenNorm}\left(p, \operatorname{compression}\left(p, Ap, Bp\right)\right)))) \Rightarrow (\forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \operatorname{schattenNorm}\left(p, \operatorname{assemble}\left(A, B\right)\right) \le \operatorname{schattenNorm}\left(p, \operatorname{compression}\left(p, A, B\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.r1_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Conjecture 1, page 2, verbatim: "Let T be a general matrix partitioned in 2 × N blocks, and let 𝒞ₚ(T) be its norm compression using the Schatten p-norm, then the following norm compression inequalities hold:" The upper branch is ‖T‖_p <= ‖𝒞ₚ(T)‖_p, p >= 2. The theorem proves the implication from this inequality for one, two and three columns to the inequality for arbitrary finite J, at the same p and row dimensions. The variables Ap and Bp represent Lean A' and B'. The empty selected family is handled separately. It proves a reduction; the unrestricted upper inequality on 2 < p < 4 remains open. The lower branch requires trace-power concavity and is not asserted here.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.assemble`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.compression`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.compressionGram`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.diagonal_power_le_eigenvalue_power`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.eigenPow`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.expectation_eq_eigenvalue_sum`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.r1_upper`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescale`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescaling_upper_three`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm_nonneg`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm_rpow`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_columnGram`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_eigenPow`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_eigenPow_rowGram`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_rowGram`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_nonneg`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_sqrt_smul`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.upper_three_columns`
