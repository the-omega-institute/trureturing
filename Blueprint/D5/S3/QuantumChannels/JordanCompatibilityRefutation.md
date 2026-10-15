# Compatibility need not imply Jordan compatibility

## Abstract

Two compatible channels on four-dimensional complex matrices need not be Jordan compatible.

**Definition 1.1 (Complex square matrices).**

$$\forall (iota: \operatorname{Type}*), (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(iota\right) = \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an index type of any universe, Mat is the type of complex square matrices on that type.

**Definition 1.2 (Complex linear maps between matrix spaces).**

$$\forall (iota: \operatorname{Type}*), (\forall (\kappa: \operatorname{Type}*), (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(iota, \kappa\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}\left(iota, \kappa, \mathbb{C}\right)))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.Map` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map is the MatrixMap abbreviation for complex linear maps between the two square-matrix spaces. Both index types may belong to arbitrary universes.

## Matrix conventions

The tensor index is Fin d × (Fin d × Fin d), with the reference coordinate first. Fin d includes every natural d, including zero. Products below retain this association. A centered dot denotes matrix multiplication for matrix operands and complex multiplication for scalar operands. Matrix.conjTranspose is conjugate transpose.

Matrix.IsHermitian means equality with the conjugate transpose. Matrix.PosSemidef includes Hermitian symmetry and nonnegativity of the quadratic form on every finitely supported complex vector. The inequality uses the complex order.

$$
\forall (iota: \operatorname{Type}*), (\forall (M: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(iota\right)), ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(M\right)) \Leftrightarrow (\operatorname{Matrix}.\operatorname{conjTranspose}\left(M\right) = M)))
$$

$$
\forall (iota: \operatorname{Type}*), (\forall (M: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(iota\right)), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(M\right)) \Leftrightarrow ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(M\right)) \land (\forall (x: \operatorname{Finsupp}\left(iota, \mathbb{C}\right)), (0 \le \operatorname{Finsupp}.\operatorname{sum}\left(x, \lambda (i: iota) \mapsto (\lambda (xi: \mathbb{C}) \mapsto (\operatorname{Finsupp}.\operatorname{sum}\left(x, \lambda (j: iota) \mapsto (\lambda (xj: \mathbb{C}) \mapsto (((\operatorname{Star}.\operatorname{star}\left(xi\right)) \cdot (M\left(i, j\right))) \cdot (xj)))\right)))\right))))))
$$

The channel predicate is finite Kraus form with identity normalization. The input and output index types are finite with decidable equality; no condition on an individual input matrix is imposed. Bracketed Fintype and DecidableEq assumptions are anonymous typeclass assumptions.

$$
\forall (\alpha: \operatorname{Type}), (\forall (\beta: \operatorname{Type}), ([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)] [\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)] (\forall (T: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(\alpha\right) \to \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(\beta\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{PureProgramQubitObstruction}.\operatorname{IsChannel}\left(T\right)) \Leftrightarrow (\exists (r: \mathbb{N}), (\exists (K: \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\beta, \alpha, \mathbb{C}\right)), ((\sum_{(k: \operatorname{Fin}\left(r\right))} ((\operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(k\right)\right)) \cdot (K\left(k\right))) = (1: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(\alpha\right))) \land (\forall (R: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(\alpha\right)), (T\left(R\right) = \sum_{(k: \operatorname{Fin}\left(r\right))} (((K\left(k\right)) \cdot (R)) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(k\right)\right))))))))))))
$$

The two partial traces of a joint output sum over its first and second coordinates, respectively.

$$
\forall (d: \mathbb{N}), (\forall (R: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\forall (p: \operatorname{Fin}\left(d\right)), (\forall (q: \operatorname{Fin}\left(d\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceLeft}\left(R\right)\left(p, q\right) = \sum_{(r: \operatorname{Fin}\left(d\right))} (R\left((r, p), (r, q)\right))))))
$$

$$
\forall (d: \mathbb{N}), (\forall (R: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\forall (p: \operatorname{Fin}\left(d\right)), (\forall (q: \operatorname{Fin}\left(d\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(R\right)\left(p, q\right) = \sum_{(r: \operatorname{Fin}\left(d\right))} (R\left((p, r), (q, r)\right))))))
$$

LinearMap.id acts as the identity on every input matrix. MatrixMap.kron acts on matrix units by the following finite sum, with both maps complex linear. The displayed specializations have the same input and output index type in each factor. Bracketed Fintype and DecidableEq assumptions are anonymous typeclass assumptions.

$$
\forall (d: \mathbb{N}), (\forall (R: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(\operatorname{Fin}\left(d\right)\right)), ((\operatorname{LinearMap}.\operatorname{id}: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right))\left(R\right) = R))
$$

$$
\forall (\alpha: \operatorname{Type}), (\forall (\beta: \operatorname{Type}), ([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)] [\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)] (\forall (T: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\alpha, \alpha\right)), (\forall (U: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\beta, \beta\right)), (\forall (R: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left((\alpha \times \beta)\right)), (\forall (a: \alpha), (\forall (b: \alpha), (\forall (c: \beta), (\forall (e: \beta), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}.\operatorname{kron}\left(T, U\right)\left(R, (a, c), (b, e)\right) = \sum_{(i: \alpha)} (\sum_{(j: \alpha)} (\sum_{(k: \beta)} (\sum_{(l: \beta)} (((T\left(\operatorname{Matrix}.\operatorname{single}\left(i, j, 1\right), a, b\right)) \cdot (U\left(\operatorname{Matrix}.\operatorname{single}\left(k, l, 1\right), c, e\right))) \cdot (R\left((i, k), (j, l)\right))))))))))))))))
$$

MatrixMap.choi_matrix uses output-first indices. For LinearMap.id its entries are those of the matrix unit with the second pair of coordinates as labels. This is the operator in equation (117), equivalently equation (120).

$$
\forall (d: \mathbb{N}), (\forall (p: (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))), (\forall (q: (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}.\operatorname{choi}_{matrix}\left((\operatorname{LinearMap}.\operatorname{id}: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right))\right)\left(p, q\right) = \operatorname{Matrix}.\operatorname{single}\left(p.2, q.2, 1\right)\left(p.1, q.1\right)) \land (\operatorname{Matrix}.\operatorname{single}\left(p.2, q.2, 1\right)\left(p.1, q.1\right) = \operatorname{if} ((p.1 = p.2) \land (q.1 = q.2)) \operatorname{then} 1 \operatorname{else} 0))))
$$

**Definition 1.3 (Tracing out the middle input factor).**

$$\forall (d: \mathbb{N}), (\forall (A: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left((\operatorname{Fin}\left(d\right) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)))\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{traceX1}\left(A\right) = \lambda (p: (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))) \mapsto (\lambda (q: (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))) \mapsto (\sum_{(r: \operatorname{Fin}\left(d\right))} (A\left((p.1, (r, p.2)), (q.1, (r, q.2))\right))))))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.traceX1` (`✓ std3`).

*Citation.* Mark Girard; Martin Plávala; Jamie Sikora (2021). *Jordan products of quantum channels and their compatibility*. DOI: [10.1038/s41467-021-22275-0](https://doi.org/10.1038/s41467-021-22275-0). URL: <https://arxiv.org/abs/2009.03279v1>.

*Commentary.*

Definition 25, equation (117): traceX1 sums the middle coordinate of the three-factor matrix and retains the reference and last coordinates.

**Definition 1.4 (Tracing out the last input factor).**

$$\forall (d: \mathbb{N}), (\forall (A: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left((\operatorname{Fin}\left(d\right) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)))\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{traceX2}\left(A\right) = \lambda (p: (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))) \mapsto (\lambda (q: (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))) \mapsto (\sum_{(r: \operatorname{Fin}\left(d\right))} (A\left((p.1, (p.2, r)), (q.1, (q.2, r))\right))))))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.traceX2` (`✓ std3`).

*Citation.* Mark Girard; Martin Plávala; Jamie Sikora (2021). *Jordan products of quantum channels and their compatibility*. DOI: [10.1038/s41467-021-22275-0](https://doi.org/10.1038/s41467-021-22275-0). URL: <https://arxiv.org/abs/2009.03279v1>.

*Commentary.*

Definition 25, equation (117): traceX2 sums the last coordinate and retains the reference and middle coordinates.

**Definition 1.5 (The Choi matrix of the generalized Jordan product).**

$$\forall (d: \mathbb{N}), (\forall (\phi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\forall (\psi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\forall (A: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left((\operatorname{Fin}\left(d\right) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)))\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{jordanAction}\left(\phi, \psi, A\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}.\operatorname{kron}\left((\operatorname{LinearMap}.\operatorname{id}: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}.\operatorname{kron}\left(\phi, \psi\right)\right)\left(A\right)))))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.jordanAction` (`✓ std3`).

*Citation.* Mark Girard; Martin Plávala; Jamie Sikora (2021). *Jordan products of quantum channels and their compatibility*. DOI: [10.1038/s41467-021-22275-0](https://doi.org/10.1038/s41467-021-22275-0). URL: <https://arxiv.org/abs/2009.03279v1>.

*Commentary.*

Definition 25, equation (119): apply the identity to the reference factor and the two maps to the other factors. This operation is defined on every matrix A; Hermitian symmetry and the two marginal equations enter JordanCompatible separately.

**Definition 1.6 (A joint channel with the prescribed marginals).**

$$\forall (d: \mathbb{N}), (\forall (\phi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\forall (\psi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Compatible}\left(\phi, \psi\right)) \Leftrightarrow (\exists (\Gamma: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{PureProgramQubitObstruction}.\operatorname{IsChannel}\left(\Gamma\right)) \land ((\forall (R: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(\operatorname{Fin}\left(d\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(\Gamma\left(R\right)\right) = \phi\left(R\right))) \land (\forall (R: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left(\operatorname{Fin}\left(d\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceLeft}\left(\Gamma\left(R\right)\right) = \psi\left(R\right)))))))))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.Compatible` (`✓ std3`).

*Citation.* Mark Girard; Martin Plávala; Jamie Sikora (2021). *Jordan products of quantum channels and their compatibility*. DOI: [10.1038/s41467-021-22275-0](https://doi.org/10.1038/s41467-021-22275-0). URL: <https://arxiv.org/abs/2009.03279v1>.

*Commentary.*

Compatibility means that a channel into the product output space has the two prescribed partial traces on every complex input matrix. The predicate itself requires the joint map to be a channel; the channel assumptions on the two given maps are explicit in claim.

**Definition 1.7 (A Hermitian operator with positive Jordan image).**

$$\forall (d: \mathbb{N}), (\forall (\phi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\forall (\psi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{JordanCompatible}\left(\phi, \psi\right)) \Leftrightarrow (\exists (A: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Mat}\left((\operatorname{Fin}\left(d\right) \times (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)))\right)), ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(A\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{traceX1}\left(A\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}.\operatorname{choi}_{matrix}\left((\operatorname{LinearMap}.\operatorname{id}: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right))\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{traceX2}\left(A\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}.\operatorname{choi}_{matrix}\left((\operatorname{LinearMap}.\operatorname{id}: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right))\right)) \land (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{jordanAction}\left(\phi, \psi, A\right)\right)))))))))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.JordanCompatible` (`✓ std3`).

*Citation.* Mark Girard; Martin Plávala; Jamie Sikora (2021). *Jordan products of quantum channels and their compatibility*. DOI: [10.1038/s41467-021-22275-0](https://doi.org/10.1038/s41467-021-22275-0). URL: <https://arxiv.org/abs/2009.03279v1>.

*Commentary.*

Definition 27 requires a Hermitian A satisfying both equations (117), whose generalized Jordan product is completely positive. By the Choi criterion this is positive semidefiniteness of jordanAction. A itself need not be positive semidefinite. Proposition 26 gives compatibility from these conditions for channels.

**Definition 1.8 (The conjecture following Theorem 30).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{claim}) \Leftrightarrow (\forall (d: \mathbb{N}), (\forall (\phi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\forall (\psi: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Map}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{PureProgramQubitObstruction}.\operatorname{IsChannel}\left(\phi\right)) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{PureProgramQubitObstruction}.\operatorname{IsChannel}\left(\psi\right)) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{Compatible}\left(\phi, \psi\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{JordanCompatible}\left(\phi, \psi\right))))))))$$

*Formalization.* `D5/S3/QuantumChannels/JordanCompatibilityRefutation.claim` (`✓ std3`).

*Citation.* Mark Girard; Martin Plávala; Jamie Sikora (2021). *Jordan products of quantum channels and their compatibility*. DOI: [10.1038/s41467-021-22275-0](https://doi.org/10.1038/s41467-021-22275-0). URL: <https://arxiv.org/abs/2009.03279v1>.

*Commentary.*

For every natural dimension and every pair of channels on that matrix space, compatibility implies Jordan compatibility. Theorem 30 proves this implication when both channels have inverse linear maps. The conjecture after its proof removes that invertibility hypothesis; claim states precisely this unrestricted implication.

**Theorem 1.9 (A compatible pair in dimension four).**

$$\neg (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{JordanCompatibilityRefutation}.\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/JordanCompatibilityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/girard-plavala-sikora-2021-jordan-compatibility-refutation` (refuted) by `D5/S3/QuantumChannels/JordanCompatibilityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"girard-plavala-sikora-2021-jordan-compatibility-refutation","declaration_gid":"D5/S3/QuantumChannels/JordanCompatibilityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Martin Plávala; Jamie Sikora (2021). *Jordan products of quantum channels and their compatibility*. DOI: [10.1038/s41467-021-22275-0](https://doi.org/10.1038/s41467-021-22275-0). URL: <https://arxiv.org/abs/2009.03279v1>.

*Commentary.*

Let P interchange the first and third standard basis vectors and the second and fourth, and let Q = diag(1,1,−1,−1). Both are real symmetric involutions and PQ + QP = 0. Put (S₁,S₂,S₃,S₄) = (P,−P,Q,−Q), Eᵢ = (5I + 4Sᵢ)/20 and Fⱼ = (4I + 3Sⱼ)/16. These positive semidefinite effects each sum to I. The two channels send R to diag(tr(EᵢR)) and diag(tr(FⱼR)). The joint channel sends R to the diagonal matrix with entries hᵢⱼ tr(EᵢR), where hᵢⱼ = 1/64 + (15/16)δᵢⱼ and δᵢⱼ is one when i = j and zero otherwise. Its two partial traces are the two channels.

Suppose A satisfies the two marginal equations and its Jordan image is positive semidefinite. The diagonal output blocks are positive semidefinite matrices. Multiply the four blocks with first output in {1,2} and second output in {3,4} by four, and label them Gₛₜ for s,t in {1,−1}. Their total is I, their s-weighted sum is (4/5)P, and their t-weighted sum is (3/4)Q. For Hₛₜ = (3/2)I − sP − tQ, the identity Hₛₜ = (1/4)(2I − sP − tQ)†(2I − sP − tQ) makes every Hₛₜ positive semidefinite. Consequently the sum of the real parts of tr(HₛₜGₛₜ) is at least zero. The three moment identities make the same sum equal to 6 − 16/5 − 3 = −1/5, a contradiction. Thus these compatible channels are not Jordan compatible.

## References

- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.Compatible`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.JordanCompatible`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.Map`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.Mat`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.jordanAction`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.traceX1`
- Truth anchor: `D5/S3/QuantumChannels/JordanCompatibilityRefutation.traceX2`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Quantum/Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Quantum/Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction](../Quantum/QuantumChannels/PureProgramQubitObstruction.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausCompletion](../Quantum/Recovery/KrausCompletion.md)
- Dependency: [D5/S3/QuantumContext/RankOfContextualityNonPowerTwo](../QuantumContext/RankOfContextualityNonPowerTwo.md)
