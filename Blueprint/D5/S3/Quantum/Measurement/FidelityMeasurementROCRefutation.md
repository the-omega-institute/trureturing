# The Fuchs–Caves fidelity ROC question is refuted

## Abstract

A three-dimensional fidelity measurement point lies below the optimal quantum ROC curve.

**Definition 1.1 (The optimal ROC boundary at a fixed false-positive coordinate).**

$$\forall (d: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\Sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (x: \mathbb{R}), (\forall (y: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.onOptimalROC}\left(\rho, \Sigma, x, y\right)) \Leftrightarrow (\forall (f: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((f \in \operatorname{Set.Icc}\left((0: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right)) \Rightarrow ((\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((f) \cdot (\rho)\right)\right) = x) \Rightarrow (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((f) \cdot (\Sigma)\right)\right) \le y)))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.onOptimalROC` (`✓ std3`).

*Citation.* András Bodor and Mátyás Koniorczyk (2017). *Receiver Operation Characteristics of Quantum State Discrimination*. DOI: [10.1007/s10946-017-9629-5](https://doi.org/10.1007/s10946-017-9629-5). URL: <https://arxiv.org/abs/1603.06801v1>.

*Commentary.*

The source describes the feasible ROC domain as convex and calls its upper boundary the optimal ROC curve (TeX lines 289–300). For a matrix test f, onOptimalROC requires every effect between zero and the identity whose false-positive coordinate is x to have true-positive coordinate at most y.

**Definition 1.2 (The Fuchs–Caves fidelity observable).**

$$\forall (d: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\Sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.fidelityObservable}\left(\rho, \Sigma\right) = ((\operatorname{Inv.inv}\left(\operatorname{CFC.sqrt}\left(\rho\right)\right)) \cdot (\operatorname{CFC.sqrt}\left(((\operatorname{CFC.sqrt}\left(\rho\right)) \cdot (\Sigma)) \cdot (\operatorname{CFC.sqrt}\left(\rho\right))\right))) \cdot (\operatorname{Inv.inv}\left(\operatorname{CFC.sqrt}\left(\rho\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.fidelityObservable` (`✓ std3`).

*Citation.* András Bodor and Mátyás Koniorczyk (2017). *Receiver Operation Characteristics of Quantum State Discrimination*. DOI: [10.1007/s10946-017-9629-5](https://doi.org/10.1007/s10946-017-9629-5). URL: <https://arxiv.org/abs/1603.06801v1>.

*Commentary.*

The observable is the matrix in equation (44), TeX lines 932–940: the inverse of the positive square root of the first state, followed by the positive square root of the sandwich with the second state, followed by the same inverse.

**Definition 1.3 (Cumulative measurement probability).**

$$\forall (d: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(d\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right)), (\forall (m: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (k: \operatorname{Fin}\left((d) + (1)\right)), (\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.cumulative}\left(a, m, k\right) = \operatorname{Finset.sum}\left(\operatorname{Finset.filter}\left(\lambda (i: \operatorname{Fin}\left(d\right)) \mapsto (\operatorname{Fin.val}\left(i\right) < \operatorname{Fin.val}\left(k\right)), \operatorname{Finset.univ}\left(\operatorname{Fin}\left(d\right)\right)\right), \lambda (i: \operatorname{Fin}\left(d\right)) \mapsto (\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.readout}\left(m, a\left(i\right)\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.cumulative` (`✓ std3`).

*Citation.* András Bodor and Mátyás Koniorczyk (2017). *Receiver Operation Characteristics of Quantum State Discrimination*. DOI: [10.1007/s10946-017-9629-5](https://doi.org/10.1007/s10946-017-9629-5). URL: <https://arxiv.org/abs/1603.06801v1>.

*Commentary.*

The source forms cumulative ROC coordinates by summing the ordered outcome probabilities (TeX lines 383–392). The definition sums the readout of m on the first k indices of the matrix-valued outcome family a.

**Definition 1.4 (An ordered eigenbasis of the fidelity observable).**

$$\forall (d: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\Sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (a: \operatorname{Fin}\left(d\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.isOrderedFidelityEigenbasis}\left(\rho, \Sigma, a\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(d\right)), (\operatorname{Finset.sum}\left(\operatorname{Finset.univ}\left(\operatorname{Fin}\left(d\right)\right), \lambda (j: \operatorname{Fin}\left(d\right)) \mapsto ((\operatorname{star}\left(a\left(i\right)\left(j\right)\right)) \cdot (a\left(i\right)\left(j\right)))\right) = (1: \mathbb{C}))) \land ((\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), ((i \ne j) \Rightarrow (\operatorname{Finset.sum}\left(\operatorname{Finset.univ}\left(\operatorname{Fin}\left(d\right)\right), \lambda (k: \operatorname{Fin}\left(d\right)) \mapsto ((\operatorname{star}\left(a\left(i\right)\left(k\right)\right)) \cdot (a\left(j\right)\left(k\right)))\right) = (0: \mathbb{C}))))) \land ((\forall (i: \operatorname{Fin}\left(d\right)), (\exists (r: \mathbb{R}), (\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.fidelityObservable}\left(\rho, \Sigma\right), a\left(i\right)\right) = ((\operatorname{Complex.ofReal}\left(r\right): \mathbb{C})) \cdot (a\left(i\right))))) \land (\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), ((i \le j) \Rightarrow ((\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.readout}\left(\Sigma, a\left(i\right)\right)) \cdot (\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.readout}\left(\rho, a\left(j\right)\right)) \ge (\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.readout}\left(\Sigma, a\left(j\right)\right)) \cdot (\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.readout}\left(\rho, a\left(i\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.isOrderedFidelityEigenbasis` (`✓ std3`).

*Citation.* András Bodor and Mátyás Koniorczyk (2017). *Receiver Operation Characteristics of Quantum State Discrimination*. DOI: [10.1007/s10946-017-9629-5](https://doi.org/10.1007/s10946-017-9629-5). URL: <https://arxiv.org/abs/1603.06801v1>.

*Commentary.*

The source orders measurement outcomes by decreasing likelihood ratio p_i/q_i (TeX lines 329–335). This predicate requires normalized rows, pairwise orthogonality, eigenvector equations for the fidelity observable, and the corresponding likelihood-ratio ordering.

**Definition 1.5 (Every cumulative fidelity point is optimal).**

$$(\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.claim}\left(\right)) \Leftrightarrow (\forall (d: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\Sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{Matrix.PosDef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow ((\operatorname{Matrix.PosDef}\left(\Sigma\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(\Sigma\right) = (1: \mathbb{C})) \Rightarrow (\forall (a: \operatorname{Fin}\left(d\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.isOrderedFidelityEigenbasis}\left(\rho, \Sigma, a\right)) \Rightarrow (\forall (k: \operatorname{Fin}\left((d) + (1)\right)), (\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.onOptimalROC}\left(\rho, \Sigma, \operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.cumulative}\left(a, \rho, k\right), \operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.cumulative}\left(a, \Sigma, k\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* András Bodor and Mátyás Koniorczyk (2017). *Receiver Operation Characteristics of Quantum State Discrimination*. DOI: [10.1007/s10946-017-9629-5](https://doi.org/10.1007/s10946-017-9629-5). URL: <https://arxiv.org/abs/1603.06801v1>.

*Commentary.*

The formal question asserts that for every finite dimension, every pair of positive-definite trace-one complex matrices, every ordered orthonormal eigenbasis of the fidelity observable, and every k in Fin(d + 1), the cumulative point is on the optimal ROC boundary.

**Theorem 1.6 (A qutrit counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation.claim}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bodor-koniorczyk-2017-fidelity-measurement-roc-refutation` (refuted) by `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bodor-koniorczyk-2017-fidelity-measurement-roc-refutation","declaration_gid":"D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* András Bodor and Mátyás Koniorczyk (2017). *Receiver Operation Characteristics of Quantum State Discrimination*. DOI: [10.1007/s10946-017-9629-5](https://doi.org/10.1007/s10946-017-9629-5). URL: <https://arxiv.org/abs/1603.06801v1>.

*Commentary.*

Use the displayed three-dimensional states with entries 1/20 times [[2,1,1],[1,10,1],[1,1,8]] and 1/40 times [[16,4,2],[4,20,1],[2,1,4]], and use the diagonal observable diag(2,1,1/2). The first state is positive definite because its unscaled matrix is the sum of the all-ones rank-one matrix and a positive diagonal matrix; the second is a positive diagonal congruence of the first. Direct trace calculation gives trace one for both.

The positive square-root uniqueness argument identifies the Fuchs–Caves observable with the displayed diagonal matrix. Its coordinate basis is an ordered eigenbasis: the eigenvalues are 2, 1 and 1/2, while the readout probabilities are q = (1/10, 1/2, 2/5) and p = (2/5, 1/2, 1/10), so the likelihood ratios decrease as 4, 1, 1/4. At k = 1 the cumulative point is (1/10, 2/5).

Take the rank-one effect vvᵀ/1382 with v = (37,2,−3). Its positive-semidefinite and upper-bound certificates place it in the interval [0,1]. Exact multiplication gives false-positive coordinate 1/10 and true-positive coordinate 5539/13820, while 2/5 is 5528/13820. Applying the claimed optimality at k = 1 would therefore give 5539/13820 ≤ 2/5, which is false.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.cumulative`
- Truth anchor: `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.fidelityObservable`
- Truth anchor: `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.isOrderedFidelityEigenbasis`
- Truth anchor: `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.onOptimalROC`
- Truth anchor: `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../Entanglement/AbsoluteSeparability/LowRankRays.md)
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](../Matrix/AlternativeMeanLinearization.md)
