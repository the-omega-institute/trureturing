# A correlation-minor bound fails without filter normal form

## Abstract

A separable qubit-ququart state violates the conjectured correlation-minor operator-norm bound without filter normal form.

Research note by Haobo Ma (Chrono AI, Singapore) and Wenlin Zhang (National University of Singapore and Chrono AI, Singapore), copyright 2026, CC BY 4.0. The cited primary works retain their own licenses. Peled, Te’eni, Carmi and Cohen are the primary problem authors; they are not inferred coauthors of the research note. This formal return makes no novelty endorsement, authorship-consent, correspondence, publication or submission claim. The original source intake disclosed exposure to communication framing; inherited repository context is also prior-exposed. The supplied scientific arguments and planning conclusions are fallible inputs, not independent final review.

**Definition 1.1 (The continuous rational noisy state).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyRho`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyRho` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For real t, set a = (1−t)/3 and ρₜ = a Σⱼ₌₀² Pⱼ ⊗ Eⱼⱼ + t I₈/8, using the same three projectors as the fixed counterexample below. For 0 ≤ t ≤ 1/200 this is a finite convex mixture of actual local density matrices. Its noise lower bound gives positive definiteness for t > 0; the endpoint t = 0 remains included.

**Definition 1.2 (The normalized Alice basis).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.alice`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.alice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The existing complete Hermitian basis (I,Z,X,Y)/√2 is shared by the interval and fixed witness.

**Definition 1.3 (The normalized Bob flag basis).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.bob`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.bob` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The existing four diagonal units followed by the six normalized symmetric and six skew pairs form the complete Bob basis, with trace-product normalization one.

**Definition 1.4 (The exact parameter-dependent correlation matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyCoefficients`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Put r = (4−t)/12, s = t/4 and a = (1−t)/3. The first four columns are 1/√2 times the rows (r,r,r,s), (a,−3a/5,−3a/5,0), (0,4a/5,−4a/5,0) and (0,0,0,0); the other twelve columns vanish. The coefficients are the actual complex state/observable traces, with no extra factor two.

**Theorem 1.5 (The full rational noise interval).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.rational_noisy_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.rational_noisy_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real 0 ≤ t ≤ 1/200, the theorem asserts actual separability and density, complete normalized bases, the exact correlation and Bob marginal diag(r,r,r,s), a nonuniform Bob marginal, the PSD noise lower bound, positive definiteness for positive noise and the strict third-order operator violation. The nonuniform marginal excludes filter normal form. The selected IZX/012 minor equals 16(4−t)(1−t)²/(1350√2). Its strict comparison with 3/(64√2) reduces to 512(4−t)(1−t)² > 2025. Both positive factors are bounded below over the whole interval, and the value of this difference at the upper endpoint is 574/15625. This is a uniform real-parameter proof.

**Definition 1.6 (The actual finite Schatten parameters).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.cmnP`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.cmnP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For a real p, cmnP p h C is the existing Partition.rectangularNorm of the increasing real compound after entrywise complexification. This uses the actual CFC row-Gram square root and existing schattenNorm. Every assertion below restricts finite p to p ≥ 1; infinity is the Euclidean operator norm cmnInf.

**Definition 1.7 (The increasing IZX row).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.selectedRow`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.selectedRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The row subset is {0,1,2}, in increasing order in the shared Alice basis. This exposes the original witness's row selection for actual reuse.

**Definition 1.8 (The four increasing flag minors).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.selectedCols`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.selectedCols` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The column subsets, in order, are {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}. They are the original four distinct witness selections.

**Theorem 1.9 (The existing single-row operator identity).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.single_row_opnorm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.single_row_opnorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The Euclidean operator norm of a finite real matrix supported in one specified row equals the square root of the sum of its squared entries. The existing proof is exposed unchanged and consumed by the general full-order compound correspondence.

**Theorem 1.10 (The existing single-row Schatten identity).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.single_row_schatten`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.single_row_schatten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every positive real p, the existing actual rectangular complex Schatten functional of the complexified single-row real matrix equals its Euclidean row length. The unchanged proof is exposed for the general full-order compound consumer, retaining zero entries and empty column types.

**Definition 1.11 (The exact row energy).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyMinorEnergy`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyMinorEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The energy is the sum of the squares of the four selected third minors of the actual noisyCoefficients matrix. The following theorem proves that these are all the possible nonzero entries of the only nonzero row; its square root is therefore the exact norm.

**Theorem 1.12 (Exact compounds and every Schatten norm on the interval).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.rational_compound_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.rational_compound_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For every real 0 ≤ t ≤ 1/200, the actual third compound has rank one. Every row other than IZX is zero, and in that row every column other than the four selected flag triples is zero. Put a=(1−t)/3, r=(4−t)/12 and s=t/4. The four entries are (64ra²/25,4sa²/5,−4sa²/5,24sa²/25)/(√2)³, with the stated increasing-order signs. The t=0 endpoint is retained even though the last three entries vanish.

For every finite p ≥ 1 and for infinity, the norm is exactly the square root of noisyMinorEnergy t and is strictly greater than 3/(64√2). The proof computes the actual real and complex row Gram matrices, and applies the existing rectangular Schatten power identity and CFC on a one-coordinate diagonal. All zero singular values are retained. The fourth compound is exactly zero, so all its finite p ≥ 1 norms and its infinity norm are zero.

This common exceeded number is the third-order operator threshold. It is distinct from Peled Theorem 1's third-order p=1 threshold 1/(16√2)+1/(48√6); no violation of that latter threshold is asserted here. The theorem concerns the no-FNF extension, preserving the original FNF hypothesis.

**Theorem 1.13 (The exact historical fixed specialization).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.fixed_compound_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.fixed_compound_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

At t=1/1000, noisyMinorEnergy is exactly 559341805929555807/500000000000000000000. The square of every finite p ≥ 1 third-order norm is this same number. Together with the interval theorem's equality for infinity, this strengthens the historical selected-row lower bound to exact norm equality, using the same state, bases, signs and four rational minors. The original result consumes this exact specialization in its contradiction.

**Definition 1.14 (Orthonormal Hermitian bases).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(a: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(a\right)\right) \Leftrightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Matrix.IsHermitian}\left(a\left(i\right)\right)\right)\right) \land \left(\left(m = \left(n\right)^{2}\right) \land \left(\forall \left(i: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Matrix.trace}\left(\left(a\left(i\right)\right) \cdot \left(a\left(j\right)\right)\right) = \operatorname{ite}\left(i = j, \left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.IsHermBasis` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

A family a consists of Hermitian n by n complex matrices, has exactly n squared members, and has trace-product pairing one on equal indices and zero on unequal indices. This is the Hilbert–Schmidt normalization at TeX line 177, without a factor of two. The definition itself permits zero dimensions.

**Definition 1.15 (The real correlation matrix).**

$$\forall \left(da: \mathbb{N}\right), \left(\forall \left(db: \mathbb{N}\right), \left(\forall \left(ma: \mathbb{N}\right), \left(\forall \left(mb: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \mathbb{C}\right)\right), \left(\forall \left(a: \left(\operatorname{Fin}\left(ma\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \left(\operatorname{Fin}\left(mb\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.corr}\left(\rho, a, b\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(ma\right), \operatorname{Fin}\left(mb\right), \mathbb{R}\right)\right) = \left(\lambda \left(i: \operatorname{Fin}\left(ma\right)\right) \mapsto \left(\left(\lambda \left(j: \operatorname{Fin}\left(mb\right)\right) \mapsto \left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(\operatorname{Matrix.kroneckerMap}\left(\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(\left(x1\right) \cdot \left(x2\right)\right)\right)\right)\right), a\left(i\right), b\left(j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.corr` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

For a complex matrix ρ on the product of the two local index spaces and local matrix families a and b, the correlation entry is the real part of the trace of ρ times the Kronecker product of a i and b j. For a density matrix and Hermitian local observables, this is the source's correlation matrix at TeX lines 179–183. The formula defines real entries for arbitrary input matrices and families as well.

**Definition 1.16 (The matrix of ordered minors).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.compound}\left(h, c\right): \operatorname{Matrix}\left(\{\left(r: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right) // \operatorname{Finset.card}\left(r\right) = h\}, \{\left(s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) // \operatorname{Finset.card}\left(s\right) = h\}, \mathbb{R}\right)\right) = \left(\lambda \left(r: \{\left(r: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right) // \operatorname{Finset.card}\left(r\right) = h\}\right) \mapsto \left(\left(\lambda \left(s: \{\left(s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) // \operatorname{Finset.card}\left(s\right) = h\}\right) \mapsto \left(\operatorname{Matrix.det}\left(\operatorname{Matrix.submatrix}\left(c, \operatorname{DFunLike.coe}\left(\operatorname{Finset.orderEmbOfFin}\left(\operatorname{Subtype.val}\left(r\right), \operatorname{Subtype.property}\left(r\right)\right)\right), \operatorname{DFunLike.coe}\left(\operatorname{Finset.orderEmbOfFin}\left(\operatorname{Subtype.val}\left(s\right), \operatorname{Subtype.property}\left(s\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.compound` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

Rows and columns are indexed by finite subsets of cardinality h. Each entry is the determinant of the submatrix whose rows and columns are enumerated increasingly by Finset.orderEmbOfFin. This specifies the signs of the minors. It is the compound matrix described at TeX lines 214–225, extended to every natural h.

**Definition 1.17 (The correlation-minor operator norm).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.cmnInf}\left(h, c\right): \mathbb{R}\right) = \left\lVert \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.compound}\left(h, c\right) \right\rVert\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.cmnInf` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The quantity cmnInf is the Euclidean operator norm of the h-th compound matrix. It is the Schatten infinity norm in the correlation-minor construction at TeX lines 225–233 and in Theorem 3 at lines 274–280. The norm acts between the Euclidean spaces indexed by the column and row subsets.

**Definition 1.18 (The proposed separability bound).**

$$\forall \left(da: \mathbb{N}\right), \left(\forall \left(db: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.bound}\left(da, db, h\right): \mathbb{R}\right) = \left(\frac{\left(1: \mathbb{R}\right)}{\operatorname{Real.sqrt}\left(\left(\operatorname{Max.max}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) \cdot \left(\operatorname{Min.min}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right)\right)}\right) \cdot \left(\left(\left(\frac{\left(\operatorname{Max.max}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) - \left(\left(1: \mathbb{R}\right)\right)}{\left(\operatorname{Max.max}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) \cdot \left(\left(\left(\operatorname{Nat.cast}\left(h\right): \mathbb{R}\right)\right) - \left(\left(1: \mathbb{R}\right)\right)\right)}\right) \cdot \left(\frac{\left(\operatorname{Min.min}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) - \left(\left(1: \mathbb{R}\right)\right)}{\left(\operatorname{Min.min}\left(\left(\operatorname{Nat.cast}\left(da\right): \mathbb{R}\right), \left(\operatorname{Nat.cast}\left(db\right): \mathbb{R}\right)\right)\right) \cdot \left(\left(\left(\operatorname{Nat.cast}\left(h\right): \mathbb{R}\right)\right) - \left(\left(1: \mathbb{R}\right)\right)\right)}\right)\right)^{\frac{\left(\left(\operatorname{Nat.cast}\left(h\right): \mathbb{R}\right)\right) - \left(\left(1: \mathbb{R}\right)\right)}{\left(2: \mathbb{R}\right)}}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.bound` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The larger and smaller local dimensions determine the right hand side of Theorem 3 at TeX lines 275–280. The dimensions are included in the real numbers, and the exponent is real: subtract one from the real value of h, then divide by two. In particular, the subtraction is not truncated natural subtraction. The expression is defined for all natural arguments, using real division and real powers.

**Definition 1.19 (The conjecture without filter normal form).**

$$\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.claim}\right) \Leftrightarrow \left(\forall \left(da: \mathbb{N}\right), \left(\forall \left(db: \mathbb{N}\right), \left(\forall \left(h: \mathbb{N}\right), \left(\left(2 \le da\right) \Rightarrow \left(\left(2 \le db\right) \Rightarrow \left(\left(\left(\operatorname{Max.max}\left(da, db\right)\right) \cdot \left(\operatorname{Min.min}\left(da, db\right)\right) \le \left(h\right)^{2}\right) \Rightarrow \left(\left(h \le \left(\operatorname{Min.min}\left(da, db\right)\right)^{2}\right) \Rightarrow \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(db\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.IsSeparable}\left(\rho\right)\right) \Rightarrow \left(\forall \left(a: \left(\operatorname{Fin}\left(\left(da\right)^{2}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \left(\operatorname{Fin}\left(\left(db\right)^{2}\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(a\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.IsHermBasis}\left(b\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.cmnInf}\left(h, \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.corr}\left(\rho, a, b\right)\right) \le \operatorname{D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation.bound}\left(da, db, h\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim` (`✓ std3`).

*Citation.* Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen (2021). *Correlation minor norms, entanglement detection and discord*. DOI: [10.1038/s41598-021-82303-3](https://doi.org/10.1038/s41598-021-82303-3). URL: <https://arxiv.org/abs/2005.12079v2>.

*Commentary.*

The conjecture at TeX line 281 removes filter normal form from Theorem 3. Here both local dimensions are at least two, the natural order h satisfies the product-dimension lower bound on h squared and the smaller-dimension-squared upper bound, and ρ is any separable state. Separability means a finite convex combination of tensor products of positive semidefinite trace-one local matrices. For every pair of normalized Hermitian bases the correlation-minor operator norm is asserted to obey the bound. There is no condition of filter normal form.

**Theorem 1.20 (A separable qubit-ququart counterexample).**

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
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.alice`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.bob`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.cmnInf`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.cmnP`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.compound`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.corr`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.fixed_compound_energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyCoefficients`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyMinorEnergy`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.noisyRho`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.rational_compound_family`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.rational_noisy_family`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.selectedCols`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.selectedRow`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.single_row_opnorm`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.single_row_schatten`
- Dependency: [D5/S3/Quantum/CotfasDVGS](../../CotfasDVGS.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../../QuantumChannels/IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/Quantum/Schatten/Partition](../../Schatten/Partition.md)
