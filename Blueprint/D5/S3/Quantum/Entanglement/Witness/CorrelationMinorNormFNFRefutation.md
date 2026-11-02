# A correlation-minor bound fails without filter normal form

## Abstract

A separable qubit-ququart state violates the conjectured correlation-minor operator-norm bound without filter normal form.

**Definition 1.1 (Orthonormal Hermitian bases).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(a: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(a\right)\right) \Leftrightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Matrix.IsHermitian}\left(a\left(i\right)\right)\right)\right) \land \left(\left(m = \left(n\right)^{2}\right) \land \left(\forall \left(i: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Matrix.trace}\left(\left(a\left(i\right)\right) \cdot \left(a\left(j\right)\right)\right) = \operatorname{ite}\left(i = j, \left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.IsHermBasis` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

A family a consists of Hermitian n by n complex matrices, has exactly n squared members, and has trace-product pairing one on equal indices and zero on unequal indices. This is the Hilbert–Schmidt normalization at TeX line 177, without a factor of two. The definition itself permits zero dimensions.

**Definition 1.2 (The real correlation matrix).**

$$\forall \left(da: \mathbb{N}\right), \left(\forall \left(db: \mathbb{N}\right), \left(\forall \left(ma: \mathbb{N}\right), \left(\forall \left(mb: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \mathbb{C}\right)\right), \left(\forall \left(a: \left(\operatorname{Fin}\left(ma\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \left(\operatorname{Fin}\left(mb\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.corr}\left(\rho, a, b\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(ma\right), \operatorname{Fin}\left(mb\right), \mathbb{R}\right)\right) = \left(\lambda \left(i: \operatorname{Fin}\left(ma\right)\right) \mapsto \left(\left(\lambda \left(j: \operatorname{Fin}\left(mb\right)\right) \mapsto \left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(\operatorname{Matrix.kroneckerMap}\left(\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(\left(x1\right) \cdot \left(x2\right)\right)\right)\right)\right), a\left(i\right), b\left(j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.corr` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For a complex matrix ρ on the product of the two local index spaces and local matrix families a and b, the correlation entry is the real part of the trace of ρ times the Kronecker product of a i and b j. For a density matrix and Hermitian local observables, this is the source's correlation matrix at TeX lines 179–183. The formula defines real entries for arbitrary input matrices and families as well.

**Definition 1.3 (The matrix of ordered minors).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.compound}\left(h, c\right): \operatorname{Matrix}\left(\{\left(r: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right) // \operatorname{Finset.card}\left(r\right) = h\}, \{\left(s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) // \operatorname{Finset.card}\left(s\right) = h\}, \mathbb{R}\right)\right) = \left(\lambda \left(r: \{\left(r: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right) // \operatorname{Finset.card}\left(r\right) = h\}\right) \mapsto \left(\left(\lambda \left(s: \{\left(s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) // \operatorname{Finset.card}\left(s\right) = h\}\right) \mapsto \left(\operatorname{Matrix.det}\left(\operatorname{Matrix.submatrix}\left(c, \operatorname{DFunLike.coe}\left(\operatorname{Finset.orderEmbOfFin}\left(\operatorname{Subtype.val}\left(r\right), \operatorname{Subtype.property}\left(r\right)\right)\right), \operatorname{DFunLike.coe}\left(\operatorname{Finset.orderEmbOfFin}\left(\operatorname{Subtype.val}\left(s\right), \operatorname{Subtype.property}\left(s\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.compound` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Rows and columns are indexed by finite subsets of cardinality h. Each entry is the determinant of the submatrix whose rows and columns are enumerated increasingly by Finset.orderEmbOfFin. This specifies the signs of the minors. It is the compound matrix described at TeX lines 214–225, extended to every natural h.

**Definition 1.4 (The correlation-minor operator norm).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.cmnInf}\left(h, c\right): \mathbb{R}\right) = \left\lVert \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.compound}\left(h, c\right) \right\rVert\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.cmnInf` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The quantity cmnInf is the Euclidean operator norm of the h-th compound matrix. It is the Schatten infinity norm in the correlation-minor construction at TeX lines 225–233 and in Theorem 3 at lines 274–280. The norm acts between the Euclidean spaces indexed by the column and row subsets.

**Definition 1.5 (The proposed separability bound).**

$$\forall \left(da: \mathbb{N}\right), \left(\forall \left(db: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.bound}\left(da, db, h\right): \mathbb{R}\right) = \left(\frac{\left(1: \mathbb{R}\right)}{\operatorname{Real.sqrt}\left(\left(\operatorname{Max.max}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) \cdot \left(\operatorname{Min.min}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right)\right)}\right) \cdot \left(\left(\left(\frac{\left(\operatorname{Max.max}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) - \left(\left(1: \mathbb{R}\right)\right)}{\left(\operatorname{Max.max}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) \cdot \left(\left(\left(\operatorname{Nat.cast}\left(h\right): \mathbb{R}\right)\right) - \left(\left(1: \mathbb{R}\right)\right)\right)}\right) \cdot \left(\frac{\left(\operatorname{Min.min}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) - \left(\left(1: \mathbb{R}\right)\right)}{\left(\operatorname{Min.min}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) \cdot \left(\left(\left(\operatorname{Nat.cast}\left(h\right): \mathbb{R}\right)\right) - \left(\left(1: \mathbb{R}\right)\right)\right)}\right)\right)^{\frac{\left(\left(\operatorname{Nat.cast}\left(h\right): \mathbb{R}\right)\right) - \left(\left(1: \mathbb{R}\right)\right)}{\left(2: \mathbb{R}\right)}}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.bound` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The larger and smaller local dimensions determine the right hand side of Theorem 3 at TeX lines 275–280. The dimensions are included in the real numbers, and the exponent is real: subtract one from the real value of h, then divide by two. In particular, the subtraction is not truncated natural subtraction. The expression is defined for all natural arguments, using real division and real powers.

**Definition 1.6 (The conjecture without filter normal form).**

$$\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.claim}\right) \Leftrightarrow \left(\forall \left(da: \mathbb{N}\right), \left(\forall \left(db: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\left(2 \le da\right) \Rightarrow \left(\left(2 \le db\right) \Rightarrow \left(\left(\left(\operatorname{Max.max}\left(da, db\right)\right) \cdot \left(\operatorname{Min.min}\left(da, db\right)\right) \le \left(h\right)^{2}\right) \Rightarrow \left(\left(h \le \left(\operatorname{Min.min}\left(da, db\right)\right)^{2}\right) \Rightarrow \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.IsSeparable}\left(\rho\right)\right) \Rightarrow \left(\forall \left(a: \left(\operatorname{Fin}\left(\left(da\right)^{2}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \left(\operatorname{Fin}\left(\left(db\right)^{2}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(a\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(b\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.cmnInf}\left(h, \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.corr}\left(\rho, a, b\right)\right) \le \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.bound}\left(da, db, h\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The conjecture at TeX line 281 removes filter normal form from Theorem 3. Here both local dimensions are at least two, the natural order h satisfies the product-dimension lower bound on h squared and the smaller-dimension-squared upper bound, and ρ is any separable state. Separability means a finite convex combination of tensor products of positive semidefinite trace-one local matrices. For every pair of normalized Hermitian bases the correlation-minor operator norm is asserted to obey the bound. There is no condition of filter normal form.

**Theorem 1.7 (A separable qubit-ququart counterexample).**

$$\neg \left(\forall \left(da: \mathbb{N}\right), \left(\forall \left(db: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\left(2 \le da\right) \Rightarrow \left(\left(2 \le db\right) \Rightarrow \left(\left(\left(\operatorname{Max.max}\left(da, db\right)\right) \cdot \left(\operatorname{Min.min}\left(da, db\right)\right) \le \left(h\right)^{2}\right) \Rightarrow \left(\left(h \le \left(\operatorname{Min.min}\left(da, db\right)\right)^{2}\right) \Rightarrow \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.IsSeparable}\left(\rho\right)\right) \Rightarrow \left(\forall \left(a: \left(\operatorname{Fin}\left(\left(da\right)^{2}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \left(\operatorname{Fin}\left(\left(db\right)^{2}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(a\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(b\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.cmnInf}\left(h, \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.corr}\left(\rho, a, b\right)\right) \le \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.bound}\left(da, db, h\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/peled-teeni-carmi-cohen-2021-correlation-minor-norm-fnf` (refuted) by `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"peled-teeni-carmi-cohen-2021-correlation-minor-norm-fnf","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Take local dimensions two and four and order three. Let Eⱼⱼ be the four-dimensional diagonal matrix units. On the two-dimensional factor set P₀ = [[1,0],[0,0]], P₁ = [[1,2],[2,4]]/5 and P₂ = [[1,−2],[−2,4]]/5. Use the state ρ = (333/1000) ∑ⱼ₌₀² Pⱼ ⊗ Eⱼⱼ + I₈/8000. Each Pⱼ is positive semidefinite because it is a positive multiple of a vector outer product, and each has trace one. The Eⱼⱼ are also positive semidefinite with trace one. The maximally mixed local matrices I₂/2 and I₄/4 have the same properties. Thus ρ is a convex combination of four product density matrices, with weights 333/1000, 333/1000, 333/1000 and 1/1000.

Choose the first local basis as (I,Z,X,Y)/√2. Choose the second as the four diagonal matrix units, followed by (Eₐᵦ + Eᵦₐ)/√2 and (−iEₐᵦ + iEᵦₐ)/√2 for the six pairs a < b, in the order (0,1), (0,2), (0,3), (1,2), (1,3), (2,3). Conjugate transposition verifies that every basis matrix is Hermitian; the trace products give the identity pairing. Both families have the required squared dimensions.

Computing the correlation matrix one row at a time gives a four by sixteen matrix. Its first four columns are 1/√2 times the matrix with rows (1333/4000,1333/4000,1333/4000,1/4000), (333/1000,−999/5000,−999/5000,0), (0,333/1250,−333/1250,0) and (0,0,0,0); its remaining columns vanish. Select the compound row indexed by {0,1,2} and the four distinct compound columns indexed by {0,1,2}, {0,1,3}, {0,2,3} and {1,2,3}. In increasing index order their determinants are, respectively, 147815037/1562500000, 110889/5000000000, −110889/5000000000 and 332667/12500000000, each divided by (√2)³. Their squares sum to 559341805929555807/500000000000000000000.

For any real matrix, apply its conjugate transpose to the unit coordinate vector at a selected row. The squared Euclidean norm of the resulting vector is the sum of the squared entries in that row. The operator-norm inequality and invariance under conjugate transposition bound this sum by the squared operator norm. Restricting the sum to any injectively selected columns only decreases it. Applied to the four minors above, this gives a lower bound of 559341805929555807/500000000000000000000 for the squared correlation-minor norm.

At dimensions two and four and order three, the proposed bound is 3/(64√2). Its square is 9/8192, strictly below the lower bound just obtained. If the asserted universal inequality held, its instance at this separable state and these two bases would bound the correlation-minor norm by 3/(64√2): the dimension conditions hold because 8 ≤ 9 and 3 ≤ 4. Both sides are nonnegative, so squaring would contradict the strict numerical gap. Therefore the bound does not hold for all separable states without filter normal form.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.IsHermBasis`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.cmnInf`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.compound`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.corr`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result`
- Dependency: [D5/S3/Quantum/CotfasDVGS](../../CotfasDVGS.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../../QuantumChannels/IptPptSquaredEquivalence.md)
