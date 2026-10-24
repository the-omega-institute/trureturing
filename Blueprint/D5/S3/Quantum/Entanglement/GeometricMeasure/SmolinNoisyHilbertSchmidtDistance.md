# Exact Hilbert-Schmidt distances of noisy Smolin states

## Abstract

The noisy Smolin state has an attained Hilbert-Schmidt distance for each of four partitions.

All matrices have complex entries. IsDensity means positive semidefinite with trace one. IsSeparable means a finite convex combination of products of density matrices for the two indicated factors. The Pauli family sigma has sigma 0 equal to the identity and sigma 1, sigma 2, sigma 3 equal to the X, Y, Z Pauli matrices, respectively. Matrix.kroneckerMap with the displayed complex multiplication function is the Kronecker product. Scalar multiplication is written with a dot; the scalar's type distinguishes real from complex scalar multiplication. DFunLike.coe explicitly turns an equivalence into its underlying function.

**Definition 1.1 (Four-qubit coordinates).**

$$Q = \operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four binary coordinates are associated to the right. This fixes the ordering of all four tensor factors.

**Definition 1.2 (The Smolin matrix).**

$$(\operatorname{smolin}: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)) = (\frac{(1: \mathbb{C})}{(16: \mathbb{C})}) \cdot (((1: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right))) + (((\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((1: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((1: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((1: \operatorname{Fin}\left(4\right))\right), \operatorname{sigma}\left((1: \operatorname{Fin}\left(4\right))\right)\right)\right)\right)) + (\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((2: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((2: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((2: \operatorname{Fin}\left(4\right))\right), \operatorname{sigma}\left((2: \operatorname{Fin}\left(4\right))\right)\right)\right)\right))) + (\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((3: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((3: \operatorname{Fin}\left(4\right))\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), \operatorname{sigma}\left((3: \operatorname{Fin}\left(4\right))\right), \operatorname{sigma}\left((3: \operatorname{Fin}\left(4\right))\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.smolin` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

The Smolin matrix is one sixteenth of the sum of the identity and the three fourfold Pauli products. The complex coefficient and the identity matrix are typed explicitly. This is manuscript.tex, lines 657-662.

**Definition 1.3 (Addition of white noise).**

$$\forall (p: \mathbb{R}), ((\operatorname{noisy}\left(p\right): \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)) = ((p) \cdot (\operatorname{smolin})) + ((((1: \mathbb{R})) - (p)) \cdot ((\frac{(1: \mathbb{C})}{(16: \mathbb{C})}) \cdot ((1: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.noisy` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

For any real p, noisy p is the affine combination of the Smolin matrix and the maximally mixed matrix. The coefficients p and 1-p act as real scalars. For p in the unit interval this is the noisy state of manuscript.tex, lines 669-671; the definition also gives a matrix outside that interval.

**Definition 1.4 (Separability for the partition 1:2:34).**

$$(\operatorname{SepOneOneTwo}: \operatorname{Set}\left(\operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)\right)) = \operatorname{convexHull}\left(\mathbb{R}, \{(\rho: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)) \mid (\exists (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (b: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (c: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right)), \operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{IsDensity}\left(a\right)) \land ((\operatorname{IsDensity}\left(b\right)) \land ((\operatorname{IsDensity}\left(c\right)) \land (\rho = \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), a, \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), b, c\right)\right))))))))\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.SepOneOneTwo` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

Take the real convex hull of a tensor product of two one-qubit density matrices and one two-qubit density matrix. This is the set separable for the partition {1}:{2}:{3,4} in manuscript.tex, lines 662-666. The convex hull consists of finite convex combinations.

**Definition 1.5 (Full separability).**

$$(\operatorname{SepFull}: \operatorname{Set}\left(\operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)\right)) = \operatorname{convexHull}\left(\mathbb{R}, \{(\rho: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)) \mid (\exists (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (b: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (c: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (d: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((\operatorname{IsDensity}\left(a\right)) \land ((\operatorname{IsDensity}\left(b\right)) \land ((\operatorname{IsDensity}\left(c\right)) \land ((\operatorname{IsDensity}\left(d\right)) \land (\rho = \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), a, \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), b, \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (\operatorname{x1}: \mathbb{C}) (\operatorname{x2}: \mathbb{C}) \mapsto ((\operatorname{x1}) \cdot (\operatorname{x2}))), c, d\right)\right)\right))))))))))\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.SepFull` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

Take the real convex hull of tensor products of four one-qubit density matrices, with the same right association as Q. This is separability for {1}:{2}:{3}:{4}, the four-partition in manuscript.tex, lines 662-666.

**Definition 1.6 (Separability for the partition 12:34).**

$$(\operatorname{SepTwoTwo}: \operatorname{Set}\left(\operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)\right)) = \{(\rho: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)) \mid (\operatorname{IsSeparable}\left(\operatorname{Matrix}.\operatorname{submatrix}\left(\rho, \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{Equiv}.\operatorname{prodAssoc}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right))\right)\right), \operatorname{DFunLike}.\operatorname{coe}\left(\operatorname{Equiv}.\operatorname{prodAssoc}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right))\right)\right)\right)\right))\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.SepTwoTwo` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

Reindex both matrix coordinates from (Fin 2 times Fin 2) times (Fin 2 times Fin 2) to Q, then require separability between the two pairs. The same product-associating equivalence is coerced to a function in each coordinate. This represents the partition {1,2}:{3,4} in manuscript.tex, lines 662-668.

**Definition 1.7 (Hilbert-Schmidt distance).**

$$\forall (X: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), (\forall (Y: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\operatorname{hsDist}\left(X, Y\right): \mathbb{R}) = \operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left((\operatorname{Matrix}.\operatorname{conjTranspose}\left((X) - (Y)\right)) \cdot ((X) - (Y))\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.hsDist` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

For arbitrary matrices X and Y, take the real square root of the real part of the trace of (X-Y) conjugate-transpose times (X-Y). The real part is taken before the square root. This is the Hilbert-Schmidt distance used in manuscript.tex, lines 662-665.

**Definition 1.8 (The proposed distance function).**

$$\forall (p: \mathbb{R}), ((\operatorname{f}\left(p\right): \mathbb{R}) = \operatorname{ite}\left(p \le \frac{(1: \mathbb{R})}{(3: \mathbb{R})}, (0: \mathbb{R}), (\frac{\operatorname{Real}.\operatorname{sqrt}\left((3: \mathbb{R})\right)}{(4: \mathbb{R})}) \cdot ((p) - (\frac{(1: \mathbb{R})}{(3: \mathbb{R})}))\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.f` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

The function is zero at and below one third and is affine with slope square root of three divided by four above one third. It is defined for every real p; its restriction to the unit interval is the proposed formula in manuscript.tex, lines 672-687.

**Definition 1.9 (The four attained minima).**

$$\operatorname{claim} = (\forall (p: \mathbb{R}), ((p \in \operatorname{Set}.\operatorname{Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \Rightarrow ((\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\operatorname{IsSeparable}\left(\sigma\right)) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, \operatorname{f}\left(p\right)\right)) \land ((\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\sigma \in \operatorname{SepOneOneTwo}) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, \operatorname{f}\left(p\right)\right)) \land ((\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\sigma \in \operatorname{SepFull}) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, \operatorname{f}\left(p\right)\right)) \land (\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\sigma \in \operatorname{SepTwoTwo}) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, (0: \mathbb{R})\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.claim` (`✓ std3`).

*Citation.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

For every p in [0,1], the least distance to the states separable for {1}:{2,3,4}, {1}:{2}:{3,4}, and {1}:{2}:{3}:{4} is f p. The least distance for {1,2}:{3,4} is zero. Each IsLeast assertion includes both attainment and a lower bound for every competing distance. These are the three proposed nonzero-distance cases of manuscript.tex, lines 672-687, together with the separable case stated at line 668.

**Theorem 1.10 (The exact distances and their attaining states).**

$$\forall (p: \mathbb{R}), ((p \in \operatorname{Set}.\operatorname{Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \Rightarrow ((\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\operatorname{IsSeparable}\left(\sigma\right)) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, \operatorname{f}\left(p\right)\right)) \land ((\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\sigma \in \operatorname{SepOneOneTwo}) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, \operatorname{f}\left(p\right)\right)) \land ((\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\sigma \in \operatorname{SepFull}) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, \operatorname{f}\left(p\right)\right)) \land (\operatorname{IsLeast}\left(\{(d: \mathbb{R}) \mid (\exists (\sigma: \operatorname{Matrix}\left(Q, Q, \mathbb{C}\right)), ((\sigma \in \operatorname{SepTwoTwo}) \land (d = \operatorname{hsDist}\left(\operatorname{noisy}\left(p\right), \sigma\right))))\}, (0: \mathbb{R})\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhu-huang-zhang-nie-zhao-lu-2026-smolin-hilbert-schmidt-distance` (proved) by `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhu-huang-zhang-nie-zhao-lu-2026-smolin-hilbert-schmidt-distance","declaration_gid":"D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xuanran Zhu; Keyi Huang; Chao Zhang; Xinfang Nie; Qi Zhao; Dawei Lu (2026). *Universal entanglement detection with geometrically optimal witnesses*. DOI: [10.1103/82gn-78lv](https://doi.org/10.1103/82gn-78lv). URL: <https://arxiv.org/abs/2610.17592v1>.

*Commentary.*

The distance from a matrix to itself is zero. Tensor products of density matrices remain positive semidefinite and have trace one, and every product of two density matrices is separable. Finite convex combinations of separable matrices are separable: concatenate the two finite product decompositions and multiply their weights by the two outer convex coefficients. Grouping the last two factors therefore gives SepFull contained in SepOneOneTwo, which is contained in the states separable for {1}:{2,3,4}. Grouping the first and last pairs, and reindexing, also gives SepFull contained in SepTwoTwo.

The maximally mixed matrix is the product of four copies of the one-qubit density I/2, so it is fully separable. For each Pauli matrix A, the two matrices (I+A)/2 and (I-A)/2 are density matrices. Average the eight fourfold products of these matrices for which the number of minus choices is even. Expanding the products gives (I+A tensor A tensor A tensor A)/16. Averaging these three matrices for A equal to X, Y, Z gives noisy (1/3), so this boundary matrix is fully separable. For 0 ≤ p ≤ 1/3, the identity noisy p = (3p) noisy (1/3) + (1-3p) I/16 expresses noisy p as a convex combination of two fully separable matrices.

Write C for the sum of the three fourfold Pauli products. Pauli trace orthogonality gives tr C = 0 and tr(C squared) = 48, hence Re tr(C noisy p) = 3p for every real p. To bound the same linear functional on a product a tensor b, where a is a one-qubit density and b is a three-qubit density, let B_j be the threefold product of the jth Pauli matrix. These three matrices are Hermitian involutions and anticommute in pairs. For arbitrary real coefficients t_j their weighted sum has square (sum of t_j squared) I.

Now set t_j = Re tr(B_j b), T = sum of t_j B_j, and q = sum of t_j squared. Then T is Hermitian, T squared equals qI, and Re tr(Tb) = q. Positivity of tr((T-I) conjugate-transpose (T-I) b) yields 0 ≤ q-2q+1, so q ≤ 1. The Bloch vector r of a has sum of r_j squared at most one, and its Pauli expectations are r_j. Thus Re tr(C(a tensor b)) = sum of r_j t_j ≤ 1 by Cauchy-Schwarz. Applying this bound to each product in a finite convex decomposition proves Re tr(C sigma) ≤ 1 for every state sigma separable for {1}:{2,3,4}.

The Hilbert-Schmidt trace-product inequality gives Re tr(CX) ≤ square root of 48 times hsDist X 0 for every complex matrix X. Indeed, reindex to a finite numerical index set, apply the squared trace-product bound, use C conjugate-transpose equal to C and tr(C squared) = 48, and use positivity of tr(X conjugate-transpose X). Dropping the squared imaginary part bounds the squared real part; taking square roots bounds its absolute value and hence its real part. With X = noisy p - sigma, the separable expectation bound gives 3p-1 ≤ square root of 48 times hsDist (noisy p) sigma. For p > 1/3 this is f p ≤ hsDist (noisy p) sigma, since square root of 48 equals four times square root of three. For p ≤ 1/3 the same distance lower bound is simply nonnegativity.

The difference noisy p - noisy (1/3) equals ((p-1/3)/16) C. Its squared Hilbert-Schmidt norm is ((p-1/3)/16) squared times 48. Taking the real square root gives hsDist (noisy p) (noisy (1/3)) = (square root of three divided by four) times |p-1/3|.

For the two-pair partition, let Pi_mu, with mu in Fin 4, be the four Bell projectors. Each Pauli expansion is one quarter of the sum of I and signed XX, YY, ZZ terms, with sign rows (1,-1,1), (-1,1,1), (1,1,-1), (-1,-1,-1). Each projector is a unitary conjugate of the normalized Bell density by I tensor I, Z tensor I, X tensor I, or Y tensor I, respectively. Unitary conjugation preserves positive semidefiniteness, and cyclicity of the trace gives trace one. After associating the coordinates into two pairs, expansion and cancellation of the sign terms give smolin = one quarter of the sum of Pi_mu tensor Pi_mu. This is a separable decomposition for {1,2}:{3,4}. For p in [0,1], combining it with I/16 using weights p and 1-p proves noisy p belongs to SepTwoTwo.

Finally, let K contain SepFull and be contained in the states separable for {1}:{2,3,4}. For p ≤ 1/3, choose noisy p in K and use its zero distance to itself. For p > 1/3, choose noisy (1/3) in K and use the boundary distance formula. The lower bound holds for every matrix in K, proving that f p is its least attainable distance. Apply this first to the states separable for {1}:{2,3,4}, then to SepOneOneTwo, then to SepFull. For SepTwoTwo, choose noisy p itself to attain zero; nonnegativity of every Hilbert-Schmidt distance proves the remaining lower bound.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.Q`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.SepFull`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.SepOneOneTwo`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.SepTwoTwo`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.f`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.hsDist`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.noisy`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance.smolin`
- Dependency: [D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation](../../Information/EntanglementDistanceBellDiagonalRefutation.md)
- Dependency: [D5/S3/QuantumChannels/ChannelTimeReversalNoGo](../../../QuantumChannels/ChannelTimeReversalNoGo.md)
