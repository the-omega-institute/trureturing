# Two-classical dephasing without an unbiased measurement

## Abstract

A three-level block measurement has time-dependent two-classical dephasing statistics without mutual unbiasedness.

The system and bath have coordinate types Fin d and Fin m. Matrices have complex entries, and CoeSort.coe displays the carrier of Matrix.unitaryGroup explicitly. Subtype.val gives the underlying matrix of V. The computational rank-one projectors are basisProjector j, and unitaryEvolution U X is UXUᴴ. Matrix.kroneckerMap with scalar multiplication forms the tensor product. Real times are embedded into the complex scalars by Complex.ofReal; the two casts of the natural dimension d are distinguished by their displayed types. Source line numbers refer to dephasing-v2.tex in arXiv:2211.02014v2.

**Definition 1.1 (The dephasing Hamiltonian).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Hs: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.hamiltonian}\left(Hs\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right) = \sum_{\left(j: \operatorname{Fin}\left(d\right)\right)} \left(\operatorname{Matrix.kroneckerMap}\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(\left(x1\right) \cdot \left(x2\right)\right)\right), \operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector}\left(j\right), Hs\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.hamiltonian` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

The Hamiltonian is the sum of the computational system projector tensored with its bath Hamiltonian. This is the Hamiltonian of TeX lines 130–134, specialized to rank-one coordinate projectors and finite-dimensional baths. The definition accepts arbitrary complex bath matrices; Hermiticity is a separate hypothesis of claim.

**Definition 1.2 (The joint propagator).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Hs: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\forall \left(t: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.propagator}\left(Hs, t\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right) = \operatorname{NormedSpace.exp}\left(\left(\left(-\operatorname{Complex.ofReal}\left(t\right)\right) \cdot \left(\operatorname{Complex.I}\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.hamiltonian}\left(Hs\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.propagator` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

For a time-independent Hamiltonian, the propagator at duration t is exp(−itH). NormedSpace.exp is the matrix exponential. The unitary evolution in TeX lines 70–73 uses this propagator when the Hamiltonian is constant. No sign or positivity restriction on t is part of the definition.

**Definition 1.3 (A measurement projector).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(x: \operatorname{Fin}\left(d\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(V, x\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\lambda \left(i: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\operatorname{Subtype.val}\left(V\right)\left(i, x\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.measurementProjector` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

The xth column of V determines a rank-one projector. Unitarity makes these columns an orthonormal basis, so the projectors form the sharp measurement of TeX lines 77–79, with the rank-one basis convention of lines 279–289.

**Definition 1.4 (The joint Lüders operation).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(x: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(X: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.luders}\left(V, x, X\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right) = \left(\left(\operatorname{Matrix.kroneckerMap}\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(\left(x1\right) \cdot \left(x2\right)\right)\right), \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(V, x\right), \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right)\right) \cdot \left(X\right)\right) \cdot \left(\operatorname{Matrix.kroneckerMap}\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(\left(x1\right) \cdot \left(x2\right)\right)\right), \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(V, x\right), \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.luders` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

The operation sandwiches X between the outcome projector tensored with the bath identity. It is the unnormalized Lüders operation acting only on the system, as in TeX lines 77–79. The two products are ordinary matrix products.

**Definition 1.5 (One-time statistics).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Hs: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(t_{0}: \mathbb{R}\right), \left(\forall \left(y: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(t_{1}: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob1}\left(Hs, \sigma, \rho, V, t_{0}, y, t_{1}\right): \mathbb{C}\right) = \operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.luders}\left(V, y, \operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution}\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.propagator}\left(Hs, \left(t_{1}\right) - \left(t_{0}\right)\right), \operatorname{Matrix.kroneckerMap}\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(\left(x1\right) \cdot \left(x2\right)\right)\right), \rho, \sigma\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.prob1` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

Starting from the product ρ ⊗ σ at t₀, evolve to t₁, apply the y outcome operation and take the joint trace. This is equation (2), TeX lines 78–80, for one measurement. The formula is complex-valued and is defined for arbitrary matrices ρ and σ; the density conditions are imposed in claim.

**Definition 1.6 (Two-time statistics).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Hs: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(t_{0}: \mathbb{R}\right), \left(\forall \left(y: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(t_{2}: \mathbb{R}\right), \left(\forall \left(x: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(t_{1}: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob2}\left(Hs, \sigma, \rho, V, t_{0}, y, t_{2}, x, t_{1}\right): \mathbb{C}\right) = \operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.luders}\left(V, y, \operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution}\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.propagator}\left(Hs, \left(t_{2}\right) - \left(t_{1}\right)\right), \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.luders}\left(V, x, \operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution}\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.propagator}\left(Hs, \left(t_{1}\right) - \left(t_{0}\right)\right), \operatorname{Matrix.kroneckerMap}\left(\lambda \left(x1: \mathbb{C}\right) \mapsto \left(\lambda \left(x2: \mathbb{C}\right) \mapsto \left(\left(x1\right) \cdot \left(x2\right)\right)\right), \rho, \sigma\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.prob2` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

Evolve from t₀ to t₁, apply outcome x, evolve for t₂−t₁, apply outcome y, and take the trace. The argument order records the later outcome and time first. This is the two-measurement case of equation (2), TeX lines 78–80, with no reset of the bath between measurements.

**Definition 1.7 (Consistency through two measurements).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Hs: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(t_{0}: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.twoClassical}\left(Hs, \sigma, \rho, V, t_{0}\right)\right) \Leftrightarrow \left(\forall \left(t_{1}: \mathbb{R}\right), \left(\forall \left(t_{2}: \mathbb{R}\right), \left(\left(t_{0} \le t_{1}\right) \to \left(\left(t_{1} \le t_{2}\right) \to \left(\left(\sum_{\left(x: \operatorname{Fin}\left(d\right)\right)} \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob1}\left(Hs, \sigma, \rho, V, t_{0}, x, t_{1}\right)\right) = \left(1: \mathbb{C}\right)\right) \land \left(\left(\forall \left(y: \operatorname{Fin}\left(d\right)\right), \left(\sum_{\left(x: \operatorname{Fin}\left(d\right)\right)} \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob2}\left(Hs, \sigma, \rho, V, t_{0}, y, t_{2}, x, t_{1}\right)\right) = \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob1}\left(Hs, \sigma, \rho, V, t_{0}, y, t_{2}\right)\right)\right) \land \left(\forall \left(x: \operatorname{Fin}\left(d\right)\right), \left(\sum_{\left(y: \operatorname{Fin}\left(d\right)\right)} \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob2}\left(Hs, \sigma, \rho, V, t_{0}, y, t_{2}, x, t_{1}\right)\right) = \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob1}\left(Hs, \sigma, \rho, V, t_{0}, x, t_{1}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.twoClassical` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

For every t₀ ≤ t₁ ≤ t₂, the one-time law is normalized and both marginals of the two-time law equal the corresponding one-time law. Thus omitting either measurement agrees with summing over its outcome. These are precisely the consistency requirements through two measurements in TeX lines 82–90; no assertion about three measurements is included.

**Definition 1.8 (Actual dependence on the measurement times).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Hs: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(t_{0}: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.timeDependent}\left(Hs, \sigma, \rho, V, t_{0}\right)\right) \Leftrightarrow \left(\exists \left(t_{1}: \mathbb{R}\right), \left(\exists \left(t_{2}: \mathbb{R}\right), \left(\exists \left(t_{1}': \mathbb{R}\right), \left(\exists \left(t_{2}': \mathbb{R}\right), \left(\left(t_{0} \le t_{1}\right) \land \left(\left(t_{1} \le t_{2}\right) \land \left(\left(t_{0} \le t_{1}'\right) \land \left(\left(t_{1}' \le t_{2}'\right) \land \left(\exists \left(x: \operatorname{Fin}\left(d\right)\right), \left(\exists \left(y: \operatorname{Fin}\left(d\right)\right), \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob2}\left(Hs, \sigma, \rho, V, t_{0}, y, t_{2}, x, t_{1}\right) \ne \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.prob2}\left(Hs, \sigma, \rho, V, t_{0}, y, t_{2}', x, t_{1}'\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.timeDependent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

For fixed initial data and fixed outcomes x and y, two ordered time pairs give different two-time values. Both pairs start at or after t₀. This explicit nonconstancy condition supplements the incompatibility discussed at TeX line 201.

**Definition 1.9 (Noncommuting measurement and dephasing projectors).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.notFullyCompatible}\left(V\right)\right) \Leftrightarrow \left(\exists \left(x: \operatorname{Fin}\left(d\right)\right), \left(\exists \left(j: \operatorname{Fin}\left(d\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(V, x\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector}\left(j\right)\right) \ne \left(\operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector}\left(j\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(V, x\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.notFullyCompatible` (`✓ std3`).

*Citation.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

Some measurement projector fails to commute with some computational projector. This is the failure of full compatibility in TeX line 201. The definition involves the two sharp measurements, independently of the bath state or the time parameters.

**Definition 1.10 (The proposed necessity of mutual unbiasedness).**

$$\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(Hs: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(V: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(t_{0}: \mathbb{R}\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Matrix.IsHermitian}\left(Hs\left(j\right)\right)\right)\right) \to \left(\left(\operatorname{Matrix.PosSemidef}\left(\sigma\right)\right) \to \left(\left(\operatorname{Matrix.trace}\left(\sigma\right) = \left(1: \mathbb{C}\right)\right) \to \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \to \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = \left(1: \mathbb{C}\right)\right) \to \left(\left(\forall \left(i: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(d\right)\right), \left(\left(i \ne j\right) \to \left(\rho\left(i, j\right) = \left(0: \mathbb{C}\right)\right)\right)\right)\right) \to \left(\left(\rho \ne \left(\frac{\left(1: \mathbb{C}\right)}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{C}\right)}\right) \cdot \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.notFullyCompatible}\left(V\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.twoClassical}\left(Hs, \sigma, \rho, V, t_{0}\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.timeDependent}\left(Hs, \sigma, \rho, V, t_{0}\right)\right) \to \left(\forall \left(j: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(x: \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Complex.normSq}\left(\operatorname{Subtype.val}\left(V\right)\left(j, x\right)\right) = \frac{\left(1: \mathbb{R}\right)}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

For every finite system and bath, take Hermitian bath Hamiltonians and positive semidefinite unit-trace bath and system matrices. Assume the system matrix is diagonal in the dephasing basis and differs from the maximally mixed matrix. If the measurement is not fully compatible, its statistics are two-classical and its two-time law is nonconstant, claim requires every squared measurement entry to be 1/d. This is a finite-dimensional necessity statement suggested by the conjecture at TeX line 347. The source's phase-modified Fourier family at lines 284–289 is unbiased; the displayed conclusion asks only for unbiasedness. The additional nonconstancy hypothesis makes the meaning of time dependence explicit. No positive lower bound on d or m is added to the quantified statement.

**Theorem 1.11 (A block measurement contradicts the necessity statement).**

$$\neg \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lonigro-chruscinski-2022-dephasing-two-classicality-refutation` (refuted) by `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lonigro-chruscinski-2022-dephasing-two-classicality-refutation","declaration_gid":"D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Davide Lonigro; Dariusz Chruściński (2022). *On the classicality of quantum dephasing processes*. DOI: [10.3389/frqst.2022.1090022](https://doi.org/10.3389/frqst.2022.1090022). URL: <https://arxiv.org/abs/2211.02014v2>.

*Commentary.*

Take d = 3, m = 2 and t₀ = 0. Put Z = diag(1,−1), H₀ = 0, H₁ = Z, H₂ = 2Z, σ = I₂/2 and ρ = diag(1/2,1/3,1/6). Choose the measurement columns (e₀+e₁)/√2, (e₀−e₁)/√2 and e₂, in that order. The amplitude 1/√2 is real and has square 1/2, which proves that the three-column matrix is unitary. Its projectors are the matrices with upper 2 by 2 blocks ½[[1,1],[1,1]] and ½[[1,−1],[−1,1]], and the projector onto e₂.

The bath matrix is positive definite and has trace one. The three positive diagonal entries of ρ prove positivity and sum to one. Its off-diagonal entries vanish, and its (0,0) entry is 1/2 rather than 1/3, so it is not maximally mixed. The three bath Hamiltonians are Hermitian.

On the joint coordinate (j,b), the Hamiltonian is diagonal with energy j for b = 0 and −j for b = 1. Applying the matrix exponential to this diagonal matrix gives the diagonal propagator with entries exp(−itE). Conjugating a matrix X therefore multiplies its (k,l) entry by exp(−it(Eₖ−Eₗ)). Both the initial product and the Hamiltonian are diagonal, so the initial product is stationary.

Sandwiching the initial product by an outcome projector gives pₓPₓ ⊗ σ, where (p₀,p₁,p₂) = (5/12,5/12,1/6). Taking its trace proves that the one-time law equals this same vector at every time. For the second measurement, idempotence of Pᵧ and cyclicity of the trace reduce the Lüders trace to Tr((Pᵧ ⊗ I₂)X). Inserting the entrywise evolution into this trace evaluates the two-time law at u = t₂−t₁ as the matrix [[a,b,0],[b,a,0],[0,0,1/6]], where a = 5(2+exp(iu)+exp(−iu))/48 and b = 5(2−exp(iu)−exp(−iu))/48. The row is y and the column is x.

Since a+b = 5/12, every row sum and every column sum equals the corresponding one-time value; those values sum to one. This proves all three two-classical consistency conditions. For x = y = 0, the ordered pairs (t₁,t₂) = (0,0) and (0,π) give respectively 5/12 and 0, using exp(iπ) = exp(−iπ) = −1. Thus the two-time law is nonconstant.

For the first measurement projector and the computational projector at 0, the (0,1) entries of their products in the two orders are 0 and 1/2. They do not commute. Finally the (2,0) measurement entry is zero, whose squared norm is 0 rather than 1/3. Applying claim to these matrices would force that squared norm to equal 1/3, a contradiction. The failure concerns necessity of unbiasedness; the sufficiency statement for unbiased bases in TeX lines 326–346 is not contradicted.

## A stationary five-mode application with no common reducing projection

Use the mode order (0,1,2,3,13) = (000,100,010,001,101), with coordinate projectors Pₓ. The original waiting/read model has the following real symmetric Hamiltonian K, waits U(t) = exp(−itK) for t ≥ 0, all density matrices as inputs, complete rank-one Lüders reads, finite classical outcome feedback and Stop. No phase gate, coarse-block instrument, energy measurement or additional preparation is added to this menu.

$$
K = \begin{pmatrix}0&1&1&1&0\\1&0&0&0&1\\1&0&0&0&0\\1&0&0&0&1\\0&1&0&1&0\end{pmatrix}
$$

$$
\rho\left(\varepsilon\right) = \frac{I}{5} + \left(\varepsilon\right) \cdot \left(K\right)
$$

For every real ε > 0 with 5ε‖K‖op < 1, where the norm is the Euclidean operator norm, ρ(ε) is positive semidefinite, has trace one and differs from I₅/5. Indeed, the self-adjoint bound K ≥ −‖K‖op I gives ρ(ε) ≥ (1/5−ε‖K‖op)I ≥ 0; the diagonal of K vanishes and its (0,1) entry is one. Every wait fixes ρ(ε), because it is an affine polynomial in K. A spectral unitary W gives WᴴKW = diag(λⱼ) and Wᴴρ(ε)W = diag(1/5+ελⱼ). The eigenvalues λⱼ are distinct: an eigenvector of K whose mode-1 coordinate vanishes must be zero, as follows from its five row equations; two independent eigenvectors of the same eigenvalue would yield such a vector. Consequently these density eigenvalues are nonuniform for every allowed ε.

Take the dephasing coordinates to be this passive energy frame, d = 5, m = 1, σ = [1], Hⱼ = [λⱼ], the system input Wᴴρ(ε)W, and measurement matrix V = Wᴴ. The measurement projectors are WᴴPₓW. The map X ↦ (WᴴXW) ⊗ [1], with the canonical identification of the one-dimensional bath coordinate, preserves products, adjoints, scalar multiplication, exponentials and trace. It maps K to the literal hamiltonian Hs, U(t) to propagator Hs t, and each native branch to luders V x. Thus it transports the intervened joint trace formula itself, without a reduced-channel regression or a bath reset. The change of coordinates supplies no physical operation.

$$
\begin{aligned}\left(P_{1}\right)\left(x, t_{1}\right) = \frac{1}{5}\\\left(P_{2}\right)\left(y, t_{2}, x, t_{1}\right) = \frac{\left\lvert U\left(\left(t_{2}\right) - \left(t_{1}\right)\right)_{yx}\right\rvert^{2}}{5}\end{aligned}
$$

These are prob1 and prob2 for every t₀ ≤ t₁ ≤ t₂ and every pair of outcomes, with the same fixed initial data. Stationarity gives Pₓρ(ε)Pₓ = Pₓ/5, so the first outcome has weight 1/5 and its conditional state is Pₓ. Unitarity makes every row and column sum of |U(u)ᵧₓ|² equal to one. The one-time law is therefore normalized and both two-time marginals are 1/5 for every ordered pair, proving twoClassical. The law is nonconstant: the (0,1) transition probability is zero at duration zero and positive at sufficiently small positive durations, since its real-frame amplitude has derivative one at zero. This supplies timeDependent as defined above.

The two PVMs have no nontrivial common orthogonal reducing projection. In native coordinates, a matrix Q commuting with all Pₓ is diagonal. Commuting also with K forces equality along the edges 0–1, 0–2, 0–3 and 1–13, so Q is scalar. In the energy frame, commuting with all energy projectors implies commuting with diag(λⱼ); conjugating back gives precisely the preceding pair of commutation conditions. An idempotent scalar is zero or one. The simple spectrum makes these rank-one energy projectors the distinct spectral projectors. Nevertheless the measurement is not mutually unbiased: (0,1,0,−1,0) is a nonzero zero-energy vector, and every zero-energy eigenvector has mode-0 coordinate zero by row 2 of K. Hence an entry Vⱼ₀ is zero, rather than having squared norm 1/5. Full compatibility is also excluded, since a mode projector would otherwise be a nontrivial common reducing projection.

Let D = diag(1,i,i,i,1). Then DᴴKD = iA, where A is FiveModeRealWaitSpan.generator, and DᴴU(t)D is the entrywise complex embedding of the real orthogonal matrix exp(tA). The transformed state is I₅/5+iεA; its entrywise real part equals that of I₅/5. The Hermitian-input theorem FiveModeRealResponse.five_mode_real_response_fiber therefore gives equality of every finite complete-record law. Conjugation fixes each mode projector, intertwines the waits and preserves trace; induction on RankOneFeedbackProtocol.Protocol transports the equality back, including every feedback branch and Stop. Thus the nonuniform density spectrum is invisible to this entire permitted predictive interface, rather than only to one-time populations.

This preparation aliasing does not make insertion of a measurement noninvasive. Use the native return experiment of SelfGeneratedPredictiveMemory §16: first outcome N = 000 at time 0, last outcome N at 2t, with a full intermediate mode read at t in the inserted experiment. Its first branch is exactly P_N/5. Writing p_A for the return probability from P_N without the intermediate read and p_B for the sum over its intermediate outcomes, the two joint probabilities are p_A/5 and p_B/5. In the real frame p_A = exp(2tA)₀₀² and p_B = ∑ⱼ exp(tA)₀ⱼ² exp(tA)ⱼ₀². Their difference g has g(0) = g′(0) = 0 and g″(0) = 4∑ⱼ A₀ⱼ² > 0. The derivative sign theorem followed by the mean-value theorem gives one δ > 0 for which p_B > p_A whenever 0 < t < δ. The joint insertion gap is therefore (p_B−p_A)/5 > 0, uniformly in the allowed ε. The same scalar-bath trace transport proves this three-time consistency violation in the dephasing frame. It reuses the native insertion mechanism; it asserts neither consistency at every order nor an inequality at every positive time.

This existing-result synthesis rules out the proposed repair that merely excludes nontrivial common reducing projections of the energy and mode PVMs. The block refutation above remains its own three-level result. The five-mode application supplies complex Hilbert-space density matrices, Born probabilities, Lüders branches and the fixed coherent Hamiltonian as model principles. It derives no such operations from ignorance, information conservation or the five-mode support alone. The scalar bath describes closed coherent dynamics and gives no retained-environment extension. Acquiring the required preparations, phase references and composition law from the native predictive contract remains a separate quantum-origin problem. No physical realization or literature-novelty claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.hamiltonian`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.luders`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.measurementProjector`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.notFullyCompatible`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.prob1`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.prob2`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.propagator`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.result`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.timeDependent`
- Truth anchor: `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.twoClassical`
- Dependency: [D5/S3/Observer/Existence/EmpiricalReflexiveSeparation](../../Observer/Existence/EmpiricalReflexiveSeparation.md)
- Dependency: [D5/S3/Quantum/Dynamics/PositivePauliClockOrder](../Dynamics/PositivePauliClockOrder.md)
- Dependency: [D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation](../Foundation/FuchsLogarithmBasisRefutation.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../RandomCircuits/HaarTwoCopyTwirl.md)
