# Upper norm compression reduces to three block columns

## Abstract

For every real p at least two, a finite family of compatible complex block columns admits nonnegative square-root weights supported on at most three original columns. The compression Gram matrix is unchanged and the Schatten p-norm does not decrease. Therefore the upper norm-compression inequality for one, two and three columns implies it for every finite number of columns.

**Definition 1.1 (Singular-value power sum).**

$$\forall (m : Type), \forall (n : Type), [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(m\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (p : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), \operatorname{schattenPow}\left(p, A\right) = \sum_{i \in \operatorname{Finsupp}.\operatorname{support}\left(\operatorname{LinearMap}.\operatorname{singularValues}\left(\operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A\right)\right)\right)} \operatorname{LinearMap}.\operatorname{singularValues}\left(\operatorname{Matrix}.\operatorname{toEuclideanLin}\left(A\right)\right)\left(i\right)^{p}$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2 defines the Schatten norm by ‖A‖_p = (Tr(|A|^p))^(1/p). The finite trace power is the sum of powers of LinearMap.singularValues of Matrix.toEuclideanLin A. Only nonzero singular values occur in its Finsupp.support; at the exponents used below, omitted zero values contribute zero.

**Definition 1.2 (Schatten norm).**

$$\forall (m : Type), \forall (n : Type), [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], [\operatorname{DecidableEq}\left(m\right)], [\operatorname{DecidableEq}\left(n\right)], \forall (p : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), \operatorname{schattenNorm}\left(p, A\right) = \operatorname{schattenPow}\left(p, A\right)^{\frac{1}{p}}$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2, verbatim: "For a general matrix or operator A, they are defined as" followed by ‖A‖_p = (Tr(|A|^p))^(1/p). Real.rpow is used for both powers, and 1/p is real division. The reduction only uses p >= 2, so neither p = 0 nor the infinite-exponent norm is involved.

**Definition 1.3 (Compatible block-column concatenation).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), \forall (C : (J \to Type)), \forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \forall (i : \operatorname{Sum}\left(HA, HB\right)), \forall (jk : \operatorname{Sigma}\left(C\right)), \operatorname{assemble}\left(A, B\right)\left(i, jk\right) = \operatorname{Matrix}.\operatorname{fromRows}\left(A\left(\operatorname{Sigma}.\operatorname{fst}\left(jk\right)\right), B\left(\operatorname{Sigma}.\operatorname{fst}\left(jk\right)\right)\right)\left(i, \operatorname{Sigma}.\operatorname{snd}\left(jk\right)\right)$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.assemble` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2 writes T as the two block rows (A_1,...,A_N) and (B_1,...,B_N). J indexes the columns, HA and HB index the row spaces, and C j is the column space shared by A j and B j. Sigma C concatenates these column spaces, which may have different finite dimensions. Matrix.fromRows stacks the two blocks.

**Definition 1.4 (Square-root column rescaling).**

$$\forall (m : Type), \forall (n : Type), \forall (w : \mathbb{R}), \forall (A : \operatorname{Matrix}\left(m, n, \mathbb{C}\right)), \operatorname{rescale}\left(w, A\right) = (\operatorname{Real}.\operatorname{sqrt}\left(w\right) : \mathbb{C}) \cdot A$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both blocks of column j are multiplied by the same nonnegative square root. The displayed coercion casts the real scalar to Complex. In the reduction, w j >= 0, including zero weights.

**Definition 1.5 (The two-row norm compression).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), \forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(2\right)), \forall (j : J), \operatorname{compression}\left(p, A, B\right)\left(i, j\right) = ((if (i = 0) then \operatorname{schattenNorm}\left(p, A\left(j\right)\right) else \operatorname{schattenNorm}\left(p, B\left(j\right)\right)) : \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.compression` (`✓ std3`).

*Citation.* K. M. R. Audenaert (2008). *On a norm compression inequality for 2×N partitioned block matrices*. DOI: [10.1016/j.laa.2007.08.007](https://doi.org/10.1016/j.laa.2007.08.007). URL: <https://arxiv.org/abs/math/0702186v2>.

*Commentary.*

Page 2, verbatim: "I denote by 𝒞ₚ(T) its Schatten p-norm compression," followed by the two scalar rows (‖A_1‖_p,...,‖A_N‖_p) and (‖B_1‖_p,...,‖B_N‖_p). Row i = 0 is the A row; the other element of Fin 2 is the B row. Each nonnegative real entry is cast to Complex.

**Definition 1.6 (Compression Gram matrix).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(J\right)], [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), \forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \operatorname{compressionGram}\left(p, A, B\right) = \operatorname{compression}\left(p, A, B\right) \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{compression}\left(p, A, B\right)\right)$$

*Formalization.* `D5/S3/Quantum/NormCompression/UpperBranchReduction.compressionGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The compression Gram matrix uses Matrix.conjTranspose and lives on the fixed row type Fin 2. Its entries are the sums of the squared top norms, squared bottom norms and products of the two norms.

**Theorem 1.7 (Three active weights preserve the compression Gram matrix).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(J\right)], [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(J\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), (2 \le p) \Rightarrow (\forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \exists (w : (J \to \mathbb{R})), (\forall (j : J), 0 \le w\left(j\right)) \land ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)\right) \le 3) \land ((\operatorname{compressionGram}\left(p, (fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), A\left(j\right)\right)), (fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), B\left(j\right)\right))\right) = \operatorname{compressionGram}\left(p, A, B\right)) \land (\operatorname{schattenNorm}\left(p, \operatorname{assemble}\left(A, B\right)\right) \le \operatorname{schattenNorm}\left(p, \operatorname{assemble}\left((fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), A\left(j\right)\right)), (fun (j : J) \mapsto \operatorname{rescale}\left(w\left(j\right), B\left(j\right)\right))\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescaling_upper_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three real moments are (‖A_j‖_p^2, ‖B_j‖_p^2, ‖A_j‖_p ‖B_j‖_p). A signed dependence among more than three active moment vectors gives two nonnegative boundary weights whose convex combination is the original weight. One boundary has no smaller convex Schatten power. Repeating the face move terminates with at most three active weights. Columns with both blocks zero are discarded before the face moves.

**Theorem 1.8 (At most three actual block columns).**

$$\forall (J : Type), \forall (HA : Type), \forall (HB : Type), [\operatorname{Fintype}\left(J\right)], [\operatorname{Fintype}\left(HA\right)], [\operatorname{Fintype}\left(HB\right)], [\operatorname{DecidableEq}\left(J\right)], [\operatorname{DecidableEq}\left(HA\right)], [\operatorname{DecidableEq}\left(HB\right)], \forall (C : (J \to Type)), [\forall (j : J), \operatorname{Fintype}\left(C\left(j\right)\right)], [\forall (j : J), \operatorname{DecidableEq}\left(C\left(j\right)\right)], \forall (p : \mathbb{R}), (2 \le p) \Rightarrow (\forall (A : \forall (j : J), \operatorname{Matrix}\left(HA, C\left(j\right), \mathbb{C}\right)), \forall (B : \forall (j : J), \operatorname{Matrix}\left(HB, C\left(j\right), \mathbb{C}\right)), \exists (w : (J \to \mathbb{R})), (\forall (j : J), 0 \le w\left(j\right)) \land ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)\right) \le 3) \land ((\operatorname{compressionGram}\left(p, (fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), A\left(\operatorname{val}\left(j\right)\right)\right)), (fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), B\left(\operatorname{val}\left(j\right)\right)\right))\right) = \operatorname{compressionGram}\left(p, A, B\right)) \land (\operatorname{schattenNorm}\left(p, \operatorname{assemble}\left(A, B\right)\right) \le \operatorname{schattenNorm}\left(p, \operatorname{assemble}\left((fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), A\left(\operatorname{val}\left(j\right)\right)\right)), (fun (j : \operatorname{Set}.\operatorname{Finite}.\operatorname{toFinset}\left(\operatorname{Set}.\operatorname{toFinite}\left(\operatorname{Function}.\operatorname{support}\left(w\right)\right)\right)) \mapsto \operatorname{rescale}\left(w\left(\operatorname{val}\left(j\right)\right), B\left(\operatorname{val}\left(j\right)\right)\right))\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/UpperBranchReduction.upper_three_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting to the finite support of w deletes every zero-weight column. The selected index is a subtype member, and val returns its original column index. The compression Gram matrix is exactly the original one, and the Schatten norm of the selected, rescaled block matrix is at least the original norm. The row dimensions and the individual column dimensions are unrestricted finite types.

**Theorem 1.9 (The three-column case implies the upper branch).**

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
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.r1_upper`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescale`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.rescaling_upper_three`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow`
- Truth anchor: `D5/S3/Quantum/NormCompression/UpperBranchReduction.upper_three_columns`
