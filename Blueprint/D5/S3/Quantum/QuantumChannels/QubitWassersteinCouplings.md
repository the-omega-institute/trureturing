# QubitWassersteinCouplings

## Abstract

Qubit coupling optimization and the exact Pauli self cost.

**Definition 1.1 (couplings).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{couplings}\left(rho, omega\right) = \{pi : \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right) | ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(pi\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(pi\right) = 1)) \land ((\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(pi\right) = omega) \land (\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceLeft}\left(pi\right) = \operatorname{Matrix}.\operatorname{transpose}\left(rho\right)))\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.couplings` (`✓ std3`).

*Citation.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The source §1.2 coupling set consists of positive semidefinite trace-one matrices on the product index type, with second-factor trace omega and first-factor trace rho transpose. The partialTraceRight and partialTraceLeft are literally the explicit sums over the traced-out factor.

**Definition 1.2 (cost).**

$$\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall pi \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right),\; \operatorname{cost}\left(A, pi\right) = \sum_{j : \operatorname{Fin}\left(k\right)} (\operatorname{RCLike}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(((\operatorname{Matrix}.\operatorname{kronecker}\left(A\left(j\right), 1\right) - \operatorname{Matrix}.\operatorname{kronecker}\left(1, \operatorname{Matrix}.\operatorname{transpose}\left(A\left(j\right)\right)\right)) \cdot (pi)) \cdot (\operatorname{Matrix}.\operatorname{kronecker}\left(A\left(j\right), 1\right) - \operatorname{Matrix}.\operatorname{kronecker}\left(1, \operatorname{Matrix}.\operatorname{transpose}\left(A\left(j\right)\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.cost` (`✓ std3`).

*Citation.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The trace cost is equation (eq:2-Wass-quant-def), with transpose on the dual factor and its real part made explicit.

**Definition 1.3 (D2).**

$$\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{D2}\left(A, rho, omega\right) = \operatorname{sInf}\left(\operatorname{Set}.\operatorname{image}\left(\operatorname{cost}\left(A\right), \operatorname{couplings}\left(rho, omega\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.D2` (`✓ std3`).

*Citation.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The quadratic quantum Wasserstein distance is the infimum in equation (eq:2-Wass-quant-def).

**Definition 1.4 (dA).**

$$\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{dA}\left(A, rho, omega\right) = \operatorname{Real}.\operatorname{sqrt}\left(\operatorname{D2}\left(A, rho, omega\right) - \frac{\operatorname{D2}\left(A, rho, rho\right) + \operatorname{D2}\left(A, omega, omega\right)}{2}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.dA` (`✓ std3`).

*Citation.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The divergence is equation (eq:mod-qw-dist-def); the displayed fraction is real division.

**Definition 1.5 (CW).**

$$\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall Phi \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; \operatorname{CW}\left(A, Phi\right) = \operatorname{sSup}\left(\{x : \mathbb{R} | \exists rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \land (x = \operatorname{dA}\left(A, rho, Phi\left(rho\right)\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.CW` (`✓ std3`).

*Citation.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Source §5.1, PDF p. 17, verbatim: “Given a finite collections of observables 𝒜={A₁, …, Aₖ}, let us define the Wasserstein complexity of a channel Φ:𝒮(ℋ)→𝒮(ℋ) by C_W(Φ):=max_{ρ∈𝒮(ℋ)} d_𝒜(ρ, Φ(ρ)).” The finite-dimensional source maximum is encoded by the supremum of its values; CW_bddAbove supplies boundedness.

**Theorem 1.6 (product_coupling).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(omega\right)) \Rightarrow (\operatorname{Matrix}.\operatorname{kronecker}\left(omega, \operatorname{Matrix}.\operatorname{transpose}\left(rho\right)\right) \in \operatorname{couplings}\left(rho, omega\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.product_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The product of the output state and the transposed input state is an admissible coupling.

**Theorem 1.7 (couplings_nonempty).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(omega\right)) \Rightarrow (\operatorname{Set}.\operatorname{Nonempty}\left(\operatorname{couplings}\left(rho, omega\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.couplings_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Every pair of density states has a coupling.

**Theorem 1.8 (D2_le_cost).**

$$\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall pi \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\left(j\right)\right)) \Rightarrow ((pi \in \operatorname{couplings}\left(rho, omega\right)) \Rightarrow (\operatorname{D2}\left(A, rho, omega\right) \le \operatorname{cost}\left(A, pi\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.D2_le_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Every admissible coupling bounds the infimum from above.

**Theorem 1.9 (pauli_hermitian).**

$$\forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pauli_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Every observable in the Pauli triple is Hermitian.

**Theorem 1.10 (ptrace2_left).**

$$\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall P \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; \operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(((\operatorname{Matrix}.\operatorname{kronecker}\left(U, 1\right)) \cdot (P)) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{Matrix}.\operatorname{kronecker}\left(U, 1\right)\right))\right) = ((U) \cdot (\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(P\right))) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(U\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.ptrace2_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Conjugating a two-qubit operator by a local matrix on the first factor conjugates its second-factor partial trace by that matrix.

**Definition 1.11 (overlap).**

$$\forall P \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; \operatorname{overlap}\left(P\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{Function}.\operatorname{uncurry}\left((1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(P, \operatorname{Function}.\operatorname{uncurry}\left((1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.overlap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The unnormalized Bell overlap is the quadratic form of P on Function.uncurry of the identity matrix.

**Theorem 1.12 (pauli_cost).**

$$\forall P \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; \operatorname{cost}\left(\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}, P\right) = (8) \cdot (\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(P\right)\right)) - (4) \cdot (\operatorname{overlap}\left(P\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pauli_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The Pauli cost operator is 8 times the identity minus 4 times the unnormalized Bell rank-one operator, equivalently 8 times the difference of the identity and the normalized Bell projector.

**Theorem 1.13 (CW_bddAbove).**

$$\forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall Phi \in \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(A\left(j\right)\right)) \Rightarrow (\operatorname{BddAbove}\left(\{x : \mathbb{R} | \exists rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \land (x = \operatorname{dA}\left(A, rho, Phi\left(rho\right)\right))\}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.CW_bddAbove` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The complexity value set is bounded above, including the empty zero-dimensional domain.

**Definition 1.14 (pureCoupling).**

$$\forall d \in \mathbb{N},\; \forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{pureCoupling}\left(S\right) = \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(\operatorname{Function}.\operatorname{uncurry}\left(S\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pureCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The square-root coupling reuses the frozen rank-one density construction on the vectorized matrix.

**Theorem 1.15 (pureCoupling_psd).**

$$\forall d \in \mathbb{N},\; \forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{pureCoupling}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pureCoupling_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

A vectorized outer product is positive semidefinite.

**Theorem 1.16 (ptrace2_pure).**

$$\forall d \in \mathbb{N},\; \forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(\operatorname{pureCoupling}\left(S\right)\right) = (S) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(S\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.ptrace2_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The second-factor trace of the vectorized coupling is S times S conjugate transpose.

**Theorem 1.17 (ptrace1_pure).**

$$\forall d \in \mathbb{N},\; \forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceLeft}\left(\operatorname{pureCoupling}\left(S\right)\right) = \operatorname{Matrix}.\operatorname{transpose}\left((\operatorname{Matrix}.\operatorname{conjTranspose}\left(S\right)) \cdot (S)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.ptrace1_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The first-factor trace is the transpose of S conjugate transpose times S.

**Theorem 1.18 (overlap_pure).**

$$\forall S \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{overlap}\left(\operatorname{pureCoupling}\left(S\right)\right) = \operatorname{Complex}.\operatorname{normSq}\left(\operatorname{Matrix}.\operatorname{trace}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.overlap_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The Bell overlap of the vectorized coupling is the squared complex norm of its trace.

**Theorem 1.19 (diagState_isState).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; (0 \le a) \Rightarrow ((0 \le b) \Rightarrow ((a + b = 1) \Rightarrow (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(\operatorname{ProjectedUnistochasticDynamics}.\operatorname{diagonalState}\left(![a, b]\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.diagState_isState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Nonnegative diagonal entries summing to one give a density state.

**Theorem 1.20 (diag_self_cost).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; (0 \le a) \Rightarrow ((0 \le b) \Rightarrow ((a + b = 1) \Rightarrow (\operatorname{D2}\left(\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}, \operatorname{ProjectedUnistochasticDynamics}.\operatorname{diagonalState}\left(![a, b]\right), \operatorname{ProjectedUnistochasticDynamics}.\operatorname{diagonalState}\left(![a, b]\right)\right) = 8 - (4) \cdot ((\operatorname{Real}.\operatorname{sqrt}\left(a\right) + \operatorname{Real}.\operatorname{sqrt}\left(b\right))^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.diag_self_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The diagonal optimum is attained by the vectorized square root; the principal-minor bound gives the matching lower bound.

**Theorem 1.21 (rotate_isState).**

$$\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; ((\operatorname{Matrix}.\operatorname{conjTranspose}\left(U\right)) \cdot (U) = 1) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(\operatorname{ProjectedUnistochasticDynamics}.\operatorname{unitaryEvolution}\left(U, rho\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.rotate_isState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Unitary conjugation preserves density states.

**Theorem 1.22 (D2_rotate).**

$$\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall omega \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; ((\operatorname{Matrix}.\operatorname{conjTranspose}\left(U\right)) \cdot (U) = 1) \Rightarrow (((U) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(U\right)) = 1) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(omega\right)) \Rightarrow (\operatorname{D2}\left(\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}, \operatorname{ProjectedUnistochasticDynamics}.\operatorname{unitaryEvolution}\left(U, rho\right), \operatorname{ProjectedUnistochasticDynamics}.\operatorname{unitaryEvolution}\left(U, omega\right)\right) = \operatorname{D2}\left(\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}, rho, omega\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.D2_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

The Pauli infimum is invariant under simultaneous unitary conjugation, by transporting couplings through U tensor conjugate U.

**Theorem 1.23 (self_cost_spectral).**

$$\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\exists a \in \mathbb{R},\; \exists b \in \mathbb{R},\; (0 \le a) \land ((0 \le b) \land ((a + b = 1) \land ((\operatorname{D2}\left(\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}, rho, rho\right) = 8 - (4) \cdot ((\operatorname{Real}.\operatorname{sqrt}\left(a\right) + \operatorname{Real}.\operatorname{sqrt}\left(b\right))^{2})) \land (\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{CFC}.\operatorname{sqrt}\left(rho\right)\right)\right) = \operatorname{Real}.\operatorname{sqrt}\left(a\right) + \operatorname{Real}.\operatorname{sqrt}\left(b\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.self_cost_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Spectral reduction supplies nonnegative eigenvalues summing to one, the exact self cost and the real trace of the positive square root.

**Theorem 1.24 (self_cost).**

$$\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\operatorname{D2}\left(\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{pauli}, rho, rho\right) = 8 - (4) \cdot ((\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(\operatorname{CFC}.\operatorname{sqrt}\left(rho\right)\right)\right))^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.self_cost` (`✓ std3`). ∎

*Citation.* G. Bunth; J. Pitrik; T. Titkos; D. Virosztek (2024). *On the metric property of quantum Wasserstein divergences*. DOI: [10.1103/PhysRevA.110.022211](https://doi.org/10.1103/PhysRevA.110.022211). URL: <https://arxiv.org/abs/2402.13150v4>.

*Commentary.*

Section 4.1, Proposition 3, equation (35), states D²(ρ,ρ)=4(1−√(1−|bρ|²)); for eigenvalues (1±r)/2 this is 8−4(tr√ρ)², the displayed correspondence.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.CW`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.CW_bddAbove`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.D2`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.D2_le_cost`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.D2_rotate`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.cost`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.couplings`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.couplings_nonempty`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.dA`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.diagState_isState`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.diag_self_cost`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.overlap`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.overlap_pure`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pauli_cost`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pauli_hermitian`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.product_coupling`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.ptrace1_pure`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.ptrace2_left`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.ptrace2_pure`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pureCoupling`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.pureCoupling_psd`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.rotate_isState`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.self_cost`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings.self_cost_spectral`
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction](../Entanglement/SteeringEllipsoidFullyEntangledFraction.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
