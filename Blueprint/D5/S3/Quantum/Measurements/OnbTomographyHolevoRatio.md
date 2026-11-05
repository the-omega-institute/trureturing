# The Holevo ratio for full orthonormal tomography

## Abstract

Full orthonormal qudit tomography has NHCRB at most d+1 times HCRB.

**Definition 1.1 (A traceless Hermitian orthonormal basis).**

$$\forall (d: \mathbb{N}), (\forall (b: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsTracelessONB}\left(d, b\right)) \Leftrightarrow ((\forall (j: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\operatorname{Matrix.IsHermitian}\left(b\left(j\right)\right))) \land ((\forall (j: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\operatorname{Matrix.trace}\left(b\left(j\right)\right) = (0: \mathbb{C}))) \land (\forall (j: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\forall (k: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\operatorname{Matrix.trace}\left((b\left(j\right)) \cdot (b\left(k\right))\right) = \operatorname{ite}\left(j = k, (1: \mathbb{C}), (0: \mathbb{C})\right))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.IsTracelessONB` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

The family b consists of d squared minus one traceless Hermitian matrices. Their trace pairings are the Kronecker delta, with normalization one as in Das et al., DraftQuantumSubmission.tex, lines 2072–2074. For d at least two, adjoining the identity spans all complex d by d matrices.

**Definition 1.2 (The linear tomography model).**

$$\forall (d: \mathbb{N}), (\forall (b: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\forall (\theta: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.model}\left(d, b, \theta\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) = ((\frac{(1: \mathbb{C})}{(\operatorname{Nat.cast}\left(d\right): \mathbb{C})}) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))) + (\sum_{j: \operatorname{Fin}\left((d^{2}) - (1)\right)} (((\operatorname{Complex.ofReal}\left(\theta\left(j\right)\right): \mathbb{C})) \cdot (b\left(j\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.model` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

The real coordinates theta multiply the basis matrices, and the identity has coefficient one over d. For a traceless Hermitian orthonormal basis and d at least two this matrix has trace one; positive semidefiniteness selects the density matrices. This is the linear model of Section 5.2 of Das et al.

**Definition 1.3 (Locally unbiased operators).**

$$\forall (d: \mathbb{N}), (\forall (b: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\forall (\theta: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\mathbb{R})), (\forall (x: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsLUB}\left(d, b, \theta, x\right)) \Leftrightarrow ((\forall (k: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\operatorname{Matrix.IsHermitian}\left(x\left(k\right)\right))) \land ((\forall (k: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\operatorname{Matrix.trace}\left((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.model}\left(d, b, \theta\right)) \cdot (x\left(k\right))\right) = (\operatorname{Complex.ofReal}\left(\theta\left(k\right)\right): \mathbb{C}))) \land (\forall (j: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\forall (k: \operatorname{Fin}\left((d^{2}) - (1)\right)), (\operatorname{Matrix.trace}\left((b\left(j\right)) \cdot (x\left(k\right))\right) = \operatorname{ite}\left(j = k, (1: \mathbb{C}), (0: \mathbb{C})\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.IsLUB` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

Each x k is Hermitian. Its expectation in the model equals theta k, and its trace pairing with b j equals the Kronecker delta. These are the uncentered local unbiasedness constraints of Das et al., lines 596–602; the derivatives of the linear model are precisely the matrices b j.

**Definition 1.4 (The uncentered covariance matrix).**

$$\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.zMatrix}\left(\rho, x\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)) = \lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\lambda (k: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Matrix.trace}\left(((\rho) \cdot (x\left(j\right))) \cdot (x\left(k\right))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.zMatrix` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

For a d by d matrix rho and n operators x, the j,k entry is the trace of rho times x j times x k, in that order. The parameter square has not been subtracted. This is the matrix in Das et al., lines 658–664.

**Definition 1.5 (The entrywise imaginary part).**

$$\forall (n: \mathbb{N}), (\forall (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.imPart}\left(a\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)) = \lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\lambda (k: \operatorname{Fin}\left(n\right)) \mapsto ((\operatorname{Complex.ofReal}\left(\operatorname{Complex.im}\left(a\left(j, k\right)\right)\right): \mathbb{C})))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.imPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

Take the imaginary part of each complex entry and embed the resulting real number back into the complex numbers. Thus the trace norm can be applied to a complex matrix representing the entrywise imaginary part.

**Definition 1.6 (Admissible Hermitian blocks).**

$$\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\forall (l: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsAdmissible}\left(x, l\right)) \Leftrightarrow ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (k: \operatorname{Fin}\left(n\right)), (\operatorname{Matrix.IsHermitian}\left(l\left(j, k\right)\right)))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (k: \operatorname{Fin}\left(n\right)), (l\left(j, k\right) = l\left(k, j\right)))) \land (\operatorname{Matrix.PosSemidef}\left((\lambda (a: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(d\right)) \mapsto (\lambda (b: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(d\right)) \mapsto (((l\left(\operatorname{Prod.fst}\left(a\right), \operatorname{Prod.fst}\left(b\right)\right)) - ((x\left(\operatorname{Prod.fst}\left(a\right)\right)) \cdot (x\left(\operatorname{Prod.fst}\left(b\right)\right))))\left(\operatorname{Prod.snd}\left(a\right), \operatorname{Prod.snd}\left(b\right)\right))): \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.IsAdmissible` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

The blocks l j k are Hermitian and symmetric in the parameter indices. After flattening the parameter and quantum indices into pairs, the block matrix with blocks l j k minus x j times x k is positive semidefinite. These are the constraints in Das et al., lines 588–608.

**Definition 1.7 (The Holevo Cramer–Rao bound).**

$$\forall (d: \mathbb{N}), (\forall (b: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\forall (\theta: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.hcrb}\left(d, b, \theta\right): \mathbb{R}) = (\operatorname{sInf}\left(\{c: \mathbb{R} \mid \exists (x: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsLUB}\left(d, b, \theta, x\right)) \land (c = (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.zMatrix}\left(\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.model}\left(d, b, \theta\right), x\right)\right)\right)) + (\operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.imPart}\left(\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.zMatrix}\left(\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.model}\left(d, b, \theta\right), x\right)\right)\right))))\}\right)) - (\sum_{j: \operatorname{Fin}\left((d^{2}) - (1)\right)} (\theta\left(j\right)^{2})))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.hcrb` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

Take the infimum over all locally unbiased families of the real part of the covariance trace plus the trace norm of its entrywise imaginary part, then subtract the sum of squared real parameters. The weight is the identity. This is the infimum form of Das et al., lines 658–666; the trace norm is the trace of the positive square root of the conjugate transpose product.

**Definition 1.8 (The Nagaoka–Hayashi Cramer–Rao bound).**

$$\forall (d: \mathbb{N}), (\forall (b: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\forall (\theta: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.nhcrb}\left(d, b, \theta\right): \mathbb{R}) = (\operatorname{sInf}\left(\{c: \mathbb{R} \mid \exists (x: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\exists (l: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to ((\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsLUB}\left(d, b, \theta, x\right)) \land ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsAdmissible}\left(x, l\right)) \land (c = \operatorname{Complex.re}\left(\sum_{j: \operatorname{Fin}\left((d^{2}) - (1)\right)} (\operatorname{Matrix.trace}\left((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.model}\left(d, b, \theta\right)) \cdot (l\left(j, j\right))\right))\right)))))\}\right)) - (\sum_{j: \operatorname{Fin}\left((d^{2}) - (1)\right)} (\theta\left(j\right)^{2})))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.nhcrb` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

Take the infimum over both locally unbiased families x and admissible block families l of the real part of the sum of the traces of rho times l j j. Subtract the same parameter square. This is the identity weight bound of Das et al., lines 588–608, with the double trace written as a sum over diagonal blocks.

**Definition 1.9 (The proposed full tomography ratio bound).**

$$\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.claim} = (\forall (d: \mathbb{N}), ((2 \le d) \Rightarrow (\forall (b: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsTracelessONB}\left(d, b\right)) \Rightarrow (\forall (\theta: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\mathbb{R})), ((\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.model}\left(d, b, \theta\right)\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.nhcrb}\left(d, b, \theta\right) \le (((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) + ((1: \mathbb{R}))) \cdot (\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.hcrb}\left(d, b, \theta\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.claim` (`✓ std3`).

*Citation.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

Das et al. write, ‘we expect the attainable bound to be d+1’ and ‘Thus for the linear GMM model, we propose Rᴺᴴ[{rho_theta}] ≤ d+1’ (DraftQuantumSubmission.tex, lines 1147–1155). The formal claim covers every orthonormal traceless Hermitian basis, including the source's generalized Gell-Mann matrices: for every d at least two and every positive semidefinite model matrix, NHCRB is at most d+1 times HCRB.

**Theorem 1.10 (The ratio bound for every orthonormal basis).**

$$\forall (d: \mathbb{N}), ((2 \le d) \Rightarrow (\forall (b: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.IsTracelessONB}\left(d, b\right)) \Rightarrow (\forall (\theta: (\operatorname{Fin}\left((d^{2}) - (1)\right)) \to (\mathbb{R})), ((\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.model}\left(d, b, \theta\right)\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.nhcrb}\left(d, b, \theta\right) \le (((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) + ((1: \mathbb{R}))) \cdot (\operatorname{D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.hcrb}\left(d, b, \theta\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.result` (`✓ std3`). ∎

*Resolves.* `Problems/das-et-al-2025-onb-tomography-holevo-ratio` (proved) by `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"das-et-al-2025-onb-tomography-holevo-ratio","declaration_gid":"D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M. (2025). *Holevo Cramér-Rao bound: How close can we get without entangling measurements?*. DOI: [10.22331/q-2025-09-30-1867](https://doi.org/10.22331/q-2025-09-30-1867). URL: <https://arxiv.org/abs/2405.09622v2>.

*Commentary.*

Put rho = model d b theta and P = Re tr(rho squared). First, adjoin the identity to b. The trace pairings give a dual family, so linear independence and the dimension count give the expansion A = (tr A/d) I + sum_j tr(b j A) b j for every complex matrix A. For a locally unbiased x, the expectation equation forces tr(x k) to vanish, and the remaining pairings then force x k = b k. Conversely b itself is locally unbiased. Hence the Holevo infimum has just one cost value.

Applying the expansion to matrix units gives the contraction sum_j b j A b j = tr(A) I − A/d. At A = I this is the Casimir identity sum_j (b j) squared = ((d squared − 1)/d) I. Consequently Re tr(Z) = (d squared − 1)/d, while orthonormality gives P = 1/d + sum_j (theta j) squared. After subtracting the parameter square the real contribution is d − P.

For the imaginary contribution let Z = zMatrix rho b and A = i imPart Z = (Z − transpose Z)/2. Hermitian symmetry and cyclicity of trace make Z Hermitian; its quadratic forms are nonnegative trace pairings with rho, so Z is positive semidefinite. Trace one also gives I − rho positive semidefinite, so its covariance is I − Z and is positive semidefinite. Adding these matrices and their transposes shows I + 2A and I − 2A are positive semidefinite. The matrix A is Hermitian, and every eigenvalue therefore has absolute value at most one half. Thus its trace norm is at least twice Re tr(A squared). For the commutators c j = rho b j − b j rho, the trace pairing expansion gives sum_k tr(c j b k) squared = tr((c j) squared), and the contraction identity gives sum_j tr((c j) squared) = 2 − 2d tr(rho squared). The entries of A are tr(c j b k)/2 and satisfy A k j = −A j k. These identities give Re tr(A squared) = (dP − 1)/2. Multiplication by i preserves trace norm, proving traceNorm(imPart Z) ≥ dP − 1.

The unique locally unbiased family reduces HCRB to the real contribution plus this trace norm. Hence HCRB ≥ d − P + dP − 1 = (d − 1)(1 + P). Since P = 1/d plus a sum of squares, this implies HCRB ≥ (d squared − 1)/d.

For NHCRB use the source's feasible blocks L* j k = ((d + 1)/(d + 2)) (b j b k + b k b j + delta j k I) (Das et al., lines 2592–2616). To check the semidefinite constraint, set r = 1/(d + 1) and form the block matrix T with blocks b k b j − r b j b k. The contraction and Casimir identities give T squared = I; T is Hermitian. Its flattened matrix S is a Hermitian involution, so I + S is positive semidefinite. The matrix with blocks L* j k − b j b k equals ((d + 1)/(d + 2)) (I + S), a nonnegative multiple of that matrix. The blocks are also symmetric and Hermitian.

Summing the diagonal feasible blocks and using the Casimir identity and tr(rho) = 1 gives cost ((d squared − 1)(d + 1))/d. Every admissible cost is nonnegative: the diagonal block l j j − (x j) squared is positive semidefinite, and (x j) squared is positive semidefinite because x j is Hermitian. Their sum l j j is therefore positive semidefinite, and the trace pairing with rho is nonnegative. Thus the infimum is bounded below and is at most the feasible cost. After subtracting the parameter square, NHCRB ≤ ((d squared − 1)(d + 1))/d − sum_j (theta j) squared.

Finally discard the nonnegative parameter square from this upper bound, factor out d + 1, and multiply the Holevo lower bound by the nonnegative number d + 1. This yields NHCRB ≤ (d + 1)((d squared − 1)/d) ≤ (d + 1) HCRB.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.IsAdmissible`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.IsLUB`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.IsTracelessONB`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.hcrb`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.imPart`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.model`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.nhcrb`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.result`
- Truth anchor: `D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio.zMatrix`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../Matrix/LinGProperty/ArithmeticBound.md)
- Dependency: [D5/S3/QuantumBounds/NonlocalityDepthQuantumBound](../../QuantumBounds/NonlocalityDepthQuantumBound.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
