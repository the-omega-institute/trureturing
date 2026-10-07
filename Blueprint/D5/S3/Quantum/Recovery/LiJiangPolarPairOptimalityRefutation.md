# Li–Jiang polar-pair optimality: an exact finite-noise refutation

## Abstract

A feasible qubit rank-one encoder strictly improves the source polar pair.

**Definition 1.1 (First source parameter).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \operatorname{lambda1}\left(d, p\right) = 1 - \frac{p}{(d)^{2} - 2}$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda1` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Source Eq. 18: d is the logical dimension and p is the noise parameter.

**Definition 1.2 (Fourth source parameter).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \operatorname{lambda4}\left(d, p\right) = \frac{(d)^{2} - 1 + p}{(d)^{2}}$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda4` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Source Eq. 18; the denominator is d squared.

**Definition 1.3 (Fifth source parameter).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \operatorname{lambda5}\left(d, p\right) = \frac{1 - p}{(d)^{2}}$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda5` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Source Eq. 18; the claim restricts p to the open interval (0,1).

**Definition 1.4 (Second source parameter).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \operatorname{lambda2}\left(d, p\right) = \frac{(1 - \operatorname{lambda1}\left(d, p\right)) \cdot (((d)^{2}) \cdot (\operatorname{lambda1}\left(d, p\right)) - 1)}{((d)^{2}) \cdot (\operatorname{lambda4}\left(d, p\right))}$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda2` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Source Eq. 18, with lambda1 and lambda4 as defined above.

**Definition 1.5 (Third source parameter).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \operatorname{lambda3}\left(d, p\right) = \frac{(2) \cdot ((1 - \operatorname{lambda1}\left(d, p\right))^{2})}{((d)^{2}) \cdot (\operatorname{lambda4}\left(d, p\right))}$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda3` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Source Eq. 18, with the factor 2 in the numerator.

**Definition 1.6 (Canonical purification of the maximally mixed state).**

$$\forall d \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(d\right),\; \forall b \in \operatorname{Fin}\left(d\right),\; \operatorname{canonicalPurification}\left(d\right)\left((a,b)\right) = \operatorname{if} (a = b) \operatorname{then} ((\operatorname{sqrt}\left(d\right))^{-1}) \operatorname{else} (0)$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.canonicalPurification` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

For positive d this is the normalized purification of I/d. Physical product order is logical factor first, auxiliary factor second; star conjugates vector entries. Product indices (a,b) are ordered pairs, not tensor products of scalar indices.

**Definition 1.7 (Canonical purification projector).**

$$\forall d \in \mathbb{N},\; \operatorname{sourcePi}\left(d\right) = \operatorname{vecMulVec}\left(\operatorname{canonicalPurification}\left(d\right), \operatorname{star}\left(\operatorname{canonicalPurification}\left(d\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourcePi` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

The outer product vecMulVec(psi,star(psi)) is the source projector in Eq. 18.

**Definition 1.8 (Source positive matrix).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \operatorname{sourceQ}\left(d, p\right) = (\operatorname{sqrt}\left(d\right)) \cdot ((\operatorname{sqrt}\left(\frac{\operatorname{lambda4}\left(d, p\right)}{(d)^{2} - 1}\right)) \cdot (1 - \operatorname{sourcePi}\left(d\right)) + (\operatorname{sqrt}\left(\operatorname{lambda5}\left(d, p\right)\right)) \cdot (\operatorname{sourcePi}\left(d\right)))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceQ` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Literal Eq. 18, with identity on the code space and sourcePi on the same space. Square roots are the real nonnegative square roots, embedded into the complex matrices.

**Definition 1.9 (Right-factor trace Kraus matrices).**

$$\forall d \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(d\right),\; \forall a \in \operatorname{Fin}\left(d\right),\; \forall b \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; \operatorname{sourceD}\left(d, j\right)\left(a, (b,k)\right) = \operatorname{if} ((a = b) \land (j = k)) \operatorname{then} (1) \operatorname{else} (0)$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceD` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Eq. 19: D_j = I_L tensor bra(j). Its row a and column (b,k) entry is 1 exactly when a=b and j=k. Thus it removes the right factor.

**Definition 1.10 (Source products).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; \operatorname{sourceB}\left(d, p, (i,j)\right) = ((\operatorname{sourceQ}\left(d, p\right)) \cdot (\operatorname{conjTranspose}\left(\operatorname{sourceD}\left(d, i\right)\right))) \cdot (\operatorname{sourceD}\left(d, j\right))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceB` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Eqs. 19–21: B_ij = Q D_i adjoint D_j. The order of the two indices is retained.

**Definition 1.11 (Source orthonormal matrices).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \forall ij \in (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)),\; \operatorname{sourceE}\left(d, p, ij\right) = ((\operatorname{sqrt}\left(\operatorname{lambda4}\left(d, p\right)\right))^{-1}) \cdot (\operatorname{vecMulVec}\left((a:(\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right))\mapsto\operatorname{if} (a = ij) \operatorname{then} (1) \operatorname{else} (0)), \operatorname{star}\left(\operatorname{canonicalPurification}\left(d\right)\right)\right) - (\operatorname{sqrt}\left(\operatorname{lambda5}\left(d, p\right)\right)) \cdot (\operatorname{conjTranspose}\left(\operatorname{sourceB}\left(d, p, ij\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceE` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Literal Eq. 22, including B_ij adjoint. The ket e_ij is the product-basis vector and psi is canonicalPurification(d).

**Definition 1.12 (Actual right partial trace).**

$$\forall d \in \mathbb{N},\; \forall X \in \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right),\; \forall a \in \operatorname{Fin}\left(d\right),\; \forall b \in \operatorname{Fin}\left(d\right),\; \operatorname{rightTrace}\left(d, X\right)\left(a, b\right) = \sum_{j:\operatorname{Fin}\left(d\right)} (X\left((a,j), (b,j)\right))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.rightTrace` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

The map is partialTraceRight from the existing library. It acts on every complex input matrix and retains the left factor.

**Definition 1.13 (Source noise on all matrices).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \forall X \in \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right),\; \operatorname{sourceNoise}\left(d, p, X\right) = (\operatorname{lambda3}\left(d, p\right)) \cdot ((\operatorname{trace}\left(X\right)) \cdot (1)) + (\operatorname{lambda1}\left(d, p\right) - \operatorname{lambda3}\left(d, p\right)) \cdot (\operatorname{kronecker}\left(\operatorname{partialTraceRight}\left(((\operatorname{sourceQ}\left(d, p\right)) \cdot (X)) \cdot (\operatorname{sourceQ}\left(d, p\right))\right), 1\right)) + (\operatorname{lambda2}\left(d, p\right)) \cdot (\sum_{ij:(\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right))} (((\operatorname{sourceE}\left(d, p, ij\right)) \cdot (X)) \cdot (\operatorname{conjTranspose}\left(\operatorname{sourceE}\left(d, p, ij\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceNoise` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Literal all-matrix Eq. 23. The identity in the first term acts on the code space; the identity in the Kronecker term acts on the auxiliary factor. Neither input nor output is normalized by its trace.

**Definition 1.14 (Source polar column matrix).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \forall chi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \operatorname{sourceC}\left(d, p, chi\right) = (\operatorname{sourceQ}\left(d, p\right)) \cdot (\operatorname{of}\left((a:(\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right))\mapsto(b:\operatorname{Fin}\left(d\right)\mapsto\operatorname{if} (\operatorname{fst}\left(a\right) = b) \operatorname{then} (chi\left(\operatorname{snd}\left(a\right)\right)) \operatorname{else} (0)))\right))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceC` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Supplement Eq. S60: chi is an auxiliary vector, and sourceC is Q times the column map I tensor ket(chi).

**Definition 1.15 (Source polar encoder).**

$$\forall d \in \mathbb{N},\; \forall p \in \mathbb{R},\; \forall chi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \operatorname{sourcePolar}\left(d, p, chi\right) = (\operatorname{sourceC}\left(d, p, chi\right)) \cdot ((\operatorname{ofMatrixInverse}\left(\operatorname{CFCsqrt}\left(\operatorname{ofMatrix}\left((\operatorname{conjTranspose}\left(\operatorname{sourceC}\left(d, p, chi\right)\right)) \cdot (\operatorname{sourceC}\left(d, p, chi\right))\right)\right)\right))^{-1})$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourcePolar` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Eq. S60. CFCsqrt denotes CFC.sqrt and ofMatrixInverse denotes CStarMatrix.ofMatrix.symm. The square root is the ordered positive CFC square root of the actual Gram matrix, transported through that equivalence; the inverse is the matrix inverse.

**Definition 1.16 (Matrix action of a completely positive map).**

$$\forall a \in \operatorname{FiniteIndex},\; \forall b \in \operatorname{FiniteIndex},\; \forall f \in \operatorname{CompletelyPositiveMap}\left(\operatorname{CStarMatrix}\left(a, a, \mathbb{C}\right), \operatorname{CStarMatrix}\left(b, b, \mathbb{C}\right)\right),\; \forall X \in \operatorname{Matrix}\left(a, a, \mathbb{C}\right),\; \operatorname{matrixAction}\left(f, X\right) = \operatorname{ofMatrixInverse}\left(f\left(\operatorname{ofMatrix}\left(X\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.matrixAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

The carrier is CompletelyPositiveMap on the finite CStarMatrix algebras, so complete positivity means positivity at every amplification. FiniteIndex abbreviates an arbitrary finite index type with Fintype and DecidableEq instances. ofMatrix is CStarMatrix.ofMatrix, and ofMatrixInverse is its inverse CStarMatrix.ofMatrix.symm; they transport input and output matrices across that equivalence.

**Definition 1.17 (Trace constraint on every positive input).**

$$\forall a \in \operatorname{FiniteIndex},\; \forall b \in \operatorname{FiniteIndex},\; \forall f \in \operatorname{CompletelyPositiveMap}\left(\operatorname{CStarMatrix}\left(a, a, \mathbb{C}\right), \operatorname{CStarMatrix}\left(b, b, \mathbb{C}\right)\right),\; \operatorname{TraceNonincreasing}\left(f\right) \Leftrightarrow (\forall X \in \operatorname{Matrix}\left(a, a, \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(X\right)) \Rightarrow (\operatorname{Re}\left(\operatorname{trace}\left(\operatorname{matrixAction}\left(f, X\right)\right)\right) \le \operatorname{Re}\left(\operatorname{trace}\left(X\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.TraceNonincreasing` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Eq. 13 permits trace-nonincreasing encoding and decoding. X ranges over every positive semidefinite matrix, and Re extracts the real part of its trace.

**Definition 1.18 (Input-first Choi convention).**

$$\forall a \in \operatorname{FiniteIndex},\; \forall b \in \operatorname{FiniteIndex},\; \forall f \in \operatorname{MatrixMap}\left(a, b, \mathbb{C}\right),\; \operatorname{inputFirstChoi}\left(f\right) = \operatorname{reindex}\left(\operatorname{prodComm}\left(b, a\right), \operatorname{prodComm}\left(b, a\right), \operatorname{choiMatrix}\left(f\right)\right)$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.inputFirstChoi` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

MatrixMap denotes PhyslibLeaf.MatrixMap, and choiMatrix denotes its choi_matrix. The source's input-first convention is obtained by swapping both product indices of that output-first Choi matrix. The reindexing uses Equiv.prodComm(b,a).

**Definition 1.19 (Unrenormalized canonical-purification fidelity).**

$$\forall d \in \mathbb{N},\; \forall f \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{entanglementFidelity}\left(d, f\right) = \operatorname{Re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{canonicalPurification}\left(d\right)\right), \operatorname{mulVec}\left(\operatorname{kron}\left(f, \operatorname{id}, \operatorname{vecMulVec}\left(\operatorname{canonicalPurification}\left(d\right), \operatorname{star}\left(\operatorname{canonicalPurification}\left(d\right)\right)\right)\right), \operatorname{canonicalPurification}\left(d\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.entanglementFidelity` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

This is the source overlap for tau=I/d: apply the logical channel to the first purification factor and the identity to the reference factor, then take the real overlap. No output trace division is made, including for trace-decreasing competitors.

**Definition 1.20 (Full fixed-noise polar-pair dominance assertion).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow (\forall p \in \mathbb{R},\; (0 < p) \Rightarrow ((p < 1) \Rightarrow (\forall chi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; (\sum_{i:\operatorname{Fin}\left(d\right)} (\operatorname{normSq}\left(chi\left(i\right)\right)) = 1) \Rightarrow (\forall C \in \operatorname{CompletelyPositiveMap}\left(\operatorname{CStarMatrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{CStarMatrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right)\right),\; \forall D \in \operatorname{CompletelyPositiveMap}\left(\operatorname{CStarMatrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right), \operatorname{CStarMatrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; (\operatorname{TraceNonincreasing}\left(C\right)) \Rightarrow ((\operatorname{TraceNonincreasing}\left(D\right)) \Rightarrow ((\operatorname{rank}\left(\operatorname{inputFirstChoi}\left(\operatorname{matrixAction}\left(C\right)\right)\right) \le 1) \Rightarrow (\operatorname{entanglementFidelity}\left(d, \operatorname{comp}\left(\operatorname{matrixAction}\left(D\right), \operatorname{comp}\left(\operatorname{sourceNoise}\left(d, p\right), \operatorname{matrixAction}\left(C\right)\right)\right)\right) \le \operatorname{entanglementFidelity}\left(d, \operatorname{comp}\left(\operatorname{rightTrace}\left(d\right), \operatorname{comp}\left(\operatorname{sourceNoise}\left(d, p\right), \operatorname{ofKraus}\left((u:\operatorname{Unit}\mapsto\operatorname{sourcePolar}\left(d, p, chi\right)), (u:\operatorname{Unit}\mapsto\operatorname{sourcePolar}\left(d, p, chi\right))\right)\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.claim` (`✓ std3`).

*Citation.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

Li and Jiang, arXiv:2609.00778v1, printed p. 17 after Eq. S64: 'Exact optimality of this pair at fixed p > 0 remains open.' The antecedent is the Eq. S60 polar encoder and the actual right partial trace. The claim quantifies over every natural d >= 2, every real 0 < p < 1, every unit complex auxiliary vector chi, and every completely positive trace-nonincreasing encoder C and decoder D with input-first encoder Choi rank at most one. ofKraus denotes PhyslibLeaf.MatrixMap.of_kraus, and comp composes maps in outer-then-inner order. Competitors are arbitrary members of that class, rather than just the isometric witnesses used to refute it.

**Theorem 1.21 (A feasible qubit pair strictly improves the source polar pair).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bikun Li; Liang Jiang (2026). *High-Rank Encoding Can Improve Approximate Quantum Error Correction*. URL: <https://arxiv.org/abs/2609.00778v1>.

*Commentary.*

At d=2, p=9/13 and chi=ket(0), the source polar columns are (3ket(00)-ket(11))/sqrt(10) and ket(10). The competitor columns are (24ket(00)-7ket(11))/25 and ket(10), with the same actual right partial trace decoder. The proof identifies the positive Gram square root and its inverse, gives the actual source noise 24 complete Kraus matrices, and uses the 48 decoder-noise-encoder composite matrices. It bridges canonical-purification fidelity to the Kraus trace sum and proves both witnesses feasible in the full all-amplification CP/TNI class, with input-first encoder Choi rank at most one. The source polar fidelity is 1537/4160 + 7sqrt(10)/80; the competitor fidelity is 336031/520000. Their difference is 7(10279-3250sqrt(10))/260000 > 0, using 10279 squared minus 10 times 3250 squared = 32841. This refutes exact finite-noise dominance. It determines no global rank-one optimum and does not refute the source's optimal quadratic asymptotic coefficient.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.TraceNonincreasing`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.canonicalPurification`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.entanglementFidelity`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.inputFirstChoi`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda1`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda2`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda3`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda4`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda5`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.matrixAction`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.rightTrace`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceB`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceC`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceD`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceE`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceNoise`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourcePi`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourcePolar`
- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceQ`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
