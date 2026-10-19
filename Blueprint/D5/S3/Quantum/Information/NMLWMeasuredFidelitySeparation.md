# Strict separation of measured and Uhlmann average fidelities

## Abstract

Three qubit states have measured average pairwise fidelity above the Uhlmann average.

**Definition 1.1 (Uhlmann root fidelity).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)][\operatorname{DecidableEq}\left(n\right)]\forall rho \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall sigma \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.uhlmann}\left(rho, sigma\right) = \operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(\operatorname{CFC.sqrt}\left(rho\right) \cdot \operatorname{CFC.sqrt}\left(sigma\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.uhlmann` (`✓ std3`).

*Citation.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Proposition 3.1, page 9: "F(ρ, σ) := ‖√ρ √σ‖₁". Here CFC.sqrt is the positive matrix square root and D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm is the matrix trace norm. The index type n is finite and has decidable equality.

**Definition 1.2 (Average pairwise Uhlmann fidelity).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall rho \in \operatorname{Fin}\left(r\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.FU}\left(rho\right) = \frac{2}{(r:\mathbb{R}) \cdot ((r:\mathbb{R}) - 1)} \cdot (\sum_{i:\operatorname{Fin}\left(r\right)}\sum_{j\in \operatorname{Finset.Ioi}\left(i\right)}(\operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.uhlmann}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\left(i\right)\right)\right), \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\left(j\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.FU` (`✓ std3`).

*Citation.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Equation (5.13), page 18: "F_U(ρ_1, …, ρ_r) := (2/(r(r−1))) Σ_{i<j} F(ρ_i, ρ_j)." Finset.Ioi i selects exactly the larger indices, so each unordered pair appears once. All normalization arithmetic is real. CStarMatrix.ofMatrix.symm converts the positive trace-one DensityState values to ordinary matrices.

**Definition 1.3 (Measured average pairwise fidelity).**

$$\forall d \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall rho \in \operatorname{Fin}\left(r\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.FM}\left(rho\right) = \frac{2}{(r:\mathbb{R}) \cdot ((r:\mathbb{R}) - 1)} \cdot (\operatorname{iInf}_{P:(\Sigma_{m:\mathbb{N}}\{L:\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\mid \operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(L\right)\})}(\sum_{i:\operatorname{Fin}\left(r\right)}\sum_{j\in \operatorname{Finset.Ioi}\left(i\right)}(\operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.uhlmann}\left(\operatorname{Matrix.diagonal}\left((\operatorname{fun}x:\operatorname{Fin}\left(P.1\right)\mapsto \operatorname{Matrix.trace}\left(P.2.\operatorname{val}\left(x\right) \cdot \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\left(i\right)\right)\right)\right))\right), \operatorname{Matrix.diagonal}\left((\operatorname{fun}x:\operatorname{Fin}\left(P.1\right)\mapsto \operatorname{Matrix.trace}\left(P.2.\operatorname{val}\left(x\right) \cdot \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\left(j\right)\right)\right)\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.FM` (`✓ std3`).

*Citation.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Definition 5.40, page 32: "F_M(ρ_1, …, ρ_r) := (2/(r(r−1))) inf_{(Λ_x)_x} Σ_{i<j} F(Λ(ρ_i), Λ(ρ_j)), where Λ(ρ_i) := Σ_x Tr[Λ_x ρ_i]|x⟩⟨x| is the measurement channel induced by applying the POVM (Λ_x)_x on the state ρ_i." The infimum is one real infimum over the dependent sum of all sizes m and all POVMs on Fin m. IsPOVM requires positivity of every effect and sum equal to the identity. It is not a nested infimum with an empty inner index type.

**Definition 1.4 (The affirmative existential statement).**

$$\operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.claim} \Leftrightarrow (\exists d \in \mathbb{N},\; \exists r \in \mathbb{N},\; \exists rho \in \operatorname{Fin}\left(r\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.FU}\left(rho\right) < \operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.FM}\left(rho\right))$$

*Formalization.* `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Remark 5.45, page 34: "Furthermore, it is interesting to determine whether there exists a tuple of states for which F_M(ρ_1, …, ρ_r) > F_U(ρ_1, …, ρ_r)—we leave this as an open question." The answer quantifies natural dimensions d, tuple sizes r, and all tuples rho of DensityState (Fin d). Strict comparison is FU rho < FM rho.

**Theorem 1.5 (Three qubit states give a strict gap).**

$$\exists d \in \mathbb{N},\; \exists r \in \mathbb{N},\; \exists rho \in \operatorname{Fin}\left(r\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.FU}\left(rho\right) < \operatorname{D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.FM}\left(rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Take d = 2 and r = 3 with the matrices I/2, diag(3/4,1/4), and the matrix with diagonal entries 1/2 and off-diagonal entries 1/4. For an effect E, its trace half a and its Z and X Bloch half-coordinates b,c satisfy a ≥ 0 and b²+c² ≤ a². An affine lower bound on the real unit disc gives a sum of the three classical pair costs at least (72/25)a + (53/100)(b+c). Summing over any finite POVM cancels the Bloch coordinates and yields FM ≥ 24/25. The two by two trace-norm identity gives FU < 24/25, proving strict separation. The estimate allows arbitrary finite POVMs and does not assert the exact value of FM.

## References

- Truth anchor: `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.FM`
- Truth anchor: `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.FU`
- Truth anchor: `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.claim`
- Truth anchor: `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.result`
- Truth anchor: `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.uhlmann`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/Schatten/TraceNorm](../Schatten/TraceNorm.md)
- Dependency: [D5/S3/QuantumStates/GNSZeroPropagation](../../QuantumStates/GNSZeroPropagation.md)
