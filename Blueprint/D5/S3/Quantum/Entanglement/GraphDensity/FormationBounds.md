# FormationBounds

## Abstract

Qubit entropy, convex concurrence cost and selective finite-ensemble formation bounds.

Scalar quotients are real unless a complex cast is displayed. Fin indices are zero based. Matrix, rankOneDensity, partialTraceRight and partialTransposeB denote the actual Lean operations. All entropy values are in bits.

**Definition 1.1 (Ensemble).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \operatorname{Ensemble}\left(\rho\right)=\{N:\mathbb N;weight:\operatorname{Fin}\left(N\right)\to \mathbb R;\operatorname{nonneg}:\forall (i:\operatorname{Fin}\left(N\right)), 0\le weight(i);\operatorname{le}_{one}:\forall (i:\operatorname{Fin}\left(N\right)), weight(i)\le 1;\operatorname{total}:\sum_{i\in \operatorname{Fin}\left(N\right)} (weight(i))=1;\psi:\operatorname{Fin}\left(N\right)\to (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C;\operatorname{unit}:\forall (i:\operatorname{Fin}\left(N\right)), \sum_{x\in (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))} (\Vert \psi(i)(x)\Vert^2)=1;\operatorname{average}:\sum_{i\in \operatorname{Fin}\left(N\right)} ((weight(i):\mathbb C)\cdot \operatorname{rankOneDensity}\left(\psi(i)\right))=\rho\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.Ensemble` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The dependent record has fields N, weight, nonneg, le_one, total, psi, unit and average. Page 18: “Let ρAB be a density matrix acting on CᵖA ⊗ CᑫB, where pq = n. Let Sρ = {{pi, |ψi⟩ : i = 1, 2, ..., N} : ρAB = ∑ⁿᵢ₌₁ pi|ψi⟩AB⟨ψi|, where |ψi⟩AB ∈ CᵖA ⊗ CᑫB, 0 ≤ pi ≤ 1 and ∑ᴺᵢ₌₁ pi = 1}.” The reconstruction is read over N ensemble terms and uses Euclidean unit vectors.

**Definition 1.2 (S).**

$$\forall (p:\mathbb N), \forall (\tau:\operatorname{Matrix}\left(\operatorname{Fin}\left(p\right), \operatorname{Fin}\left(p\right), \mathbb C\right)), \operatorname{S}\left(\tau\right)=\begin{cases}\frac{\sum_{i\in \operatorname{Fin}\left(p\right)} (\operatorname{Real}.\operatorname{negMulLog}(h.\operatorname{eigenvalues}(i)))}{\operatorname{Real}.\operatorname{log}(2)}&\operatorname{if} h:\tau.\operatorname{IsHermitian}\\0&\operatorname{otherwise}\end{cases}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.S` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Page 4: “The von Neumann entropy of an n × n density matrix ρ is S(ρ) = −∑ⁿᵢ₌₁ λi(ρ) log₂ λi(ρ).” Real.negMulLog handles zero eigenvalues; division by Real.log 2 converts natural logs to bits. The non-Hermitian branch is zero and is not used for density matrices.

**Definition 1.3 (ensembleCost).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \forall (e:\operatorname{Ensemble}\left(\rho\right)), \operatorname{ensembleCost}\left(e\right)=\sum_{i\in \operatorname{Fin}\left(e.\operatorname{N}\right)} (e.\operatorname{weight}(i)\cdot \operatorname{S}\left(\operatorname{partialTraceRight}\left(\operatorname{rankOneDensity}\left(e.\operatorname{psi}(i)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.ensembleCost` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The finite weighted entropy of the literal second-factor partial traces.

**Definition 1.4 (E_F).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), E_F(\rho)=\operatorname{sInf}\left(\{t:\mathbb R\mid \exists e:\operatorname{Ensemble}\left(\rho\right),t=\operatorname{ensembleCost}\left(e\right)\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.E_F` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Page 18: “The entanglement of formation of ρAB is denoted and defined by EF(ρAB) = inf{pi,|ψi⟩:i=1,2,...,N}∈Sρ ∑ᴺᵢ₌₁ piS(trX(|ψi⟩AB⟨ψi|)), where X = A or X = B.” The real infimum uses the finite Euclidean-unit ensembles above and X = B. For a pure state the two marginals have the same nonzero spectrum, so X = A gives the same value in bits: zero eigenvalues contribute zero. The repository’s frozen D5/S3/Quantum/Information/InputInformationBalance.pure_complementary_entropy states this equality; it is not on this module’s dependency path. Spectral ensemble nonemptiness is proved below.

**Theorem 1.5 (cost_set_nonempty_iff).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \{t:\mathbb R\mid \exists e:\operatorname{Ensemble}\left(\rho\right),t=\operatorname{ensembleCost}\left(e\right)\}.\operatorname{Nonempty}\iff \operatorname{Nonempty}\left(\operatorname{Ensemble}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.cost_set_nonempty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Definition 1.6 (Analytic.f).**

$$\forall (c:\mathbb R), \operatorname{Analytic}.\operatorname{f}(c)=\operatorname{CloningMachine}.\operatorname{binaryEntropyBits}(\frac{1-\operatorname{Real}.\operatorname{sqrt}(1-(c)^{2})}{2})$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.f` (`✓ std3`).

*Citation.* William K. Wootters (1998). *Entanglement of Formation of an Arbitrary State of Two Qubits*. DOI: [10.1103/PhysRevLett.80.2245](https://doi.org/10.1103/PhysRevLett.80.2245). URL: <https://arxiv.org/abs/quant-ph/9709029v2>.

*Commentary.*

Wootters equations (6)–(8) write h(x) = Real.binEntropy(x) / Real.log(2). The frozen CloningMachine.binaryEntropyBits supplies this bit entropy.

**Theorem 1.7 (Analytic.star_root_upper).**

$$\forall (c:\mathbb R), ((0\le c)\land ((c)^{2}\le \frac{1}{64}))\longrightarrow \operatorname{Analytic}.\operatorname{f}(c)<\frac{1}{25}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.star_root_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.8 (Analytic.lower_rational).**

$$\forall (k:\mathbb N), (32\le k)\longrightarrow \frac{499751}{16646144}<\frac{7\cdot ((k:\mathbb R)-1)}{8\cdot (k:\mathbb R)-2}\cdot \operatorname{Analytic}.\operatorname{f}(\frac{8}{63})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.lower_rational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.9 (Analytic.upper_rational).**

$$\forall (q:\mathbb N), (64\le q)\longrightarrow \frac{\frac{(q:\mathbb R)}{25}+1}{2\cdot (q:\mathbb R)-1}\le \frac{89}{3175}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.upper_rational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.10 (qubit_entropy_det).**

$$\forall (\tau:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb C\right)), ((\tau.\operatorname{PosSemidef})\land (\tau.\operatorname{trace}=1))\longrightarrow \operatorname{S}\left(\tau\right)=\operatorname{CloningMachine}.\operatorname{binaryEntropyBits}(\frac{1-\operatorname{Real}.\operatorname{sqrt}(1-4\cdot \tau.\operatorname{det}.\operatorname{re})}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.qubit_entropy_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.11 (trace_outer).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (\psi:(\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C), \operatorname{rankOneDensity}\left(\psi\right).\operatorname{trace}=(\sum_{x\in (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))} (\Vert \psi(x)\Vert^2):\mathbb C)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.trace_outer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.12 (marginal_trace).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (\psi:(\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C), \operatorname{partialTraceRight}\left(\operatorname{rankOneDensity}\left(\psi\right)\right).\operatorname{trace}=(\sum_{x\in (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right))} (\Vert \psi(x)\Vert^2):\mathbb C)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.marginal_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.13 (pure_qubit_nonneg).**

$$\forall (q:\mathbb N), \forall (\psi:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C), (\sum_{x\in (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))} (\Vert \psi(x)\Vert^2)=1)\longrightarrow 0\le \operatorname{S}\left(\operatorname{partialTraceRight}\left(\operatorname{rankOneDensity}\left(\psi\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.pure_qubit_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.14 (pure_qubit_le_one).**

$$\forall (q:\mathbb N), \forall (\psi:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C), (\sum_{x\in (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))} (\Vert \psi(x)\Vert^2)=1)\longrightarrow \operatorname{S}\left(\operatorname{partialTraceRight}\left(\operatorname{rankOneDensity}\left(\psi\right)\right)\right)\le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.pure_qubit_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.15 (qubit_entropy_concave).**

$$\operatorname{ConcaveOn}\left(\mathbb R, \{\tau:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb C\right)\mid \operatorname{IsDensity}\left(\tau\right)\}, \operatorname{S}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.qubit_entropy_concave` (`✓ std3`). ∎

*Citation.* Guifré Vidal (2000). *Entanglement monotones*. DOI: [10.1080/09500340008244048](https://doi.org/10.1080/09500340008244048). URL: <https://arxiv.org/abs/quant-ph/9807077v2>.

*Commentary.*

Concavity of the marginal entropy on positive trace-one qubit matrices. The proof reduces eigenvalue entropy to the reused Bloch geometry.

**Theorem 1.16 (Analytic.f_convex).**

$$\operatorname{ConvexOn}\left(\mathbb R, \operatorname{Set}.\operatorname{Icc}(0,1), \operatorname{Analytic}.\operatorname{f}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.f_convex` (`✓ std3`). ∎

*Citation.* William K. Wootters (1998). *Entanglement of Formation of an Arbitrary State of Two Qubits*. DOI: [10.1103/PhysRevLett.80.2245](https://doi.org/10.1103/PhysRevLett.80.2245). URL: <https://arxiv.org/abs/quant-ph/9709029v2>.

*Commentary.*

Convexity on the full closed concurrence interval, including both endpoints; Wootters equations (6)–(8).

**Theorem 1.17 (spectral_ensemble_nonempty).**

$$\forall (p:\mathbb N), \forall (q:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(p\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), ((\rho.\operatorname{PosSemidef})\land (\rho.\operatorname{trace}=1))\longrightarrow \operatorname{Nonempty}\left(\operatorname{Ensemble}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.spectral_ensemble_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.18 (formation_nonneg).**

$$\forall (q:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), (\operatorname{Nonempty}\left(\operatorname{Ensemble}\left(\rho\right)\right))\longrightarrow 0\le E_F(\rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.formation_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Theorem 1.19 (formation_le_cost).**

$$\forall (q:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \forall (e:\operatorname{Ensemble}\left(\rho\right)), E_F(\rho)\le \operatorname{ensembleCost}\left(e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.formation_le_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean theorem; every displayed parameter is quantified.

**Definition 1.20 (Witness.expectation).**

$$\forall (w:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right))\to \mathbb C), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), \mathbb C\right)), \operatorname{Witness}.\operatorname{expectation}(w,\rho)=\operatorname{dotProduct}\left(\operatorname{star}\left(w\right), \operatorname{partialTransposeB}\left(\rho\right).\operatorname{mulVec}(w)\right).\operatorname{re}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.expectation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The real quadratic readout of the frozen partial transpose.

**Definition 1.21 (Witness.W).**

$$\forall (w:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right))\to \mathbb C), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), \mathbb C\right)), \operatorname{Witness}.\operatorname{W}(w,\rho)=\operatorname{max}\left(0, -\operatorname{Witness}.\operatorname{expectation}(w,\rho)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The positive part of the negative expectation.

**Definition 1.22 (Selective.restrictVec).**

$$\forall (q:\mathbb N), \forall (k:\mathbb N), \forall (part:\operatorname{Fin}\left(q\right)\to \operatorname{Fin}\left(k\right)), \forall (j:\operatorname{Fin}\left(k\right)), \forall (\psi:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C), \forall (x:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))), \operatorname{Selective}.\operatorname{restrictVec}(part,j,\psi)(x)=\operatorname{ite}\left(part(x.2)=j, \psi(x), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.restrictVec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean definition; every displayed parameter is quantified.

**Definition 1.23 (Selective.branchMass).**

$$\forall (q:\mathbb N), \forall (k:\mathbb N), \forall (part:\operatorname{Fin}\left(q\right)\to \operatorname{Fin}\left(k\right)), \forall (j:\operatorname{Fin}\left(k\right)), \forall (\psi:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C), \operatorname{Selective}.\operatorname{branchMass}(part,j,\psi)=\sum_{x\in (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))} (\Vert \operatorname{Selective}.\operatorname{restrictVec}(part,j,\psi)(x)\Vert^2)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.branchMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean definition; every displayed parameter is quantified.

**Definition 1.24 (Selective.branchVec).**

$$\forall (q:\mathbb N), \forall (k:\mathbb N), \forall (part:\operatorname{Fin}\left(q\right)\to \operatorname{Fin}\left(k\right)), \forall (j:\operatorname{Fin}\left(k\right)), \forall (\psi:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))\to \mathbb C), \operatorname{Selective}.\operatorname{branchVec}(part,j,\psi)=\operatorname{ite}\left(\operatorname{Selective}.\operatorname{branchMass}(part,j,\psi)=0, \psi, (\frac{1}{\operatorname{Real}.\operatorname{sqrt}(\operatorname{Selective}.\operatorname{branchMass}(part,j,\psi))}:\mathbb C)\cdot \operatorname{Selective}.\operatorname{restrictVec}(part,j,\psi)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.branchVec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean definition; every displayed parameter is quantified.

**Definition 1.25 (Selective.projectBlock).**

$$\forall (q:\mathbb N), \forall (k:\mathbb N), \forall (part:\operatorname{Fin}\left(q\right)\to \operatorname{Fin}\left(k\right)), \forall (j:\operatorname{Fin}\left(k\right)), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \forall (x:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))), \forall (y:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right))), \operatorname{Selective}.\operatorname{projectBlock}(part,j,\rho)(x,y)=\operatorname{ite}\left((part(x.2)=j)\land (part(y.2)=j), \rho(x,y), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.projectBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Literal Lean definition; every displayed parameter is quantified.

**Definition 1.26 (Selective.conditionalEnsemble).**

$$\forall (q:\mathbb N), \forall (k:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \forall (e:\operatorname{Ensemble}\left(\rho\right)), \forall (part:\operatorname{Fin}\left(q\right)\to \operatorname{Fin}\left(k\right)), \forall (j:\operatorname{Fin}\left(k\right)), \forall (p:\mathbb R), \forall (hp:0<p), \forall (r:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \forall (ht:r.\operatorname{trace}=1), \forall (ha:\operatorname{Selective}.\operatorname{projectBlock}(part,j,\rho)=(p:\mathbb C)\cdot r), (\operatorname{Selective}.\operatorname{conditionalEnsemble}(e,part,j,p,hp,r,ht,ha).\operatorname{N}=e.\operatorname{N})\land (\forall (i:\operatorname{Fin}\left(e.\operatorname{N}\right)), \operatorname{Selective}.\operatorname{conditionalEnsemble}(e,part,j,p,hp,r,ht,ha).\operatorname{weight}(i)=\frac{e.\operatorname{weight}(i)\cdot \operatorname{Selective}.\operatorname{branchMass}(part,j,e.\operatorname{psi}(i))}{p})\land (\forall (i:\operatorname{Fin}\left(e.\operatorname{N}\right)), \operatorname{Selective}.\operatorname{conditionalEnsemble}(e,part,j,p,hp,r,ht,ha).\operatorname{psi}(i)=\operatorname{Selective}.\operatorname{branchVec}(part,j,e.\operatorname{psi}(i)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.conditionalEnsemble` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The returned record has type Ensemble r. Its N, weight and psi fields are exactly the displayed expressions. Its nonneg, le_one, total, unit and average proof fields certify the constraints of Ensemble. The positive branch has normalized weights e.weight i · branchMass(part,j,e.psi i) / p and supplies an ensemble for each positive-probability branch.

**Theorem 1.27 (Selective.selective_formation).**

$$\forall (q:\mathbb N), \forall (k:\mathbb N), \forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), \forall (part:\operatorname{Fin}\left(q\right)\to \operatorname{Fin}\left(k\right)), \forall (p:\operatorname{Fin}\left(k\right)\to \mathbb R), \forall (r:\operatorname{Fin}\left(k\right)\to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(q\right)), \mathbb C\right)), ((\operatorname{Nonempty}\left(\operatorname{Ensemble}\left(\rho\right)\right))\land (\forall (j:\operatorname{Fin}\left(k\right)), 0\le p(j))\land (\forall (j:\operatorname{Fin}\left(k\right)), r(j).\operatorname{trace}=1)\land (\forall (j:\operatorname{Fin}\left(k\right)), \operatorname{Selective}.\operatorname{projectBlock}(part,j,\rho)=(p(j):\mathbb C)\cdot r(j)))\longrightarrow \sum_{j\in \operatorname{Fin}\left(k\right)} (p(j)\cdot E_F(r(j)))\le E_F(\rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.selective_formation` (`✓ std3`). ∎

*Citation.* Guifré Vidal (2000). *Entanglement monotones*. DOI: [10.1080/09500340008244048](https://doi.org/10.1080/09500340008244048). URL: <https://arxiv.org/abs/quant-ph/9807077v2>.

*Commentary.*

Finite projective partitions on the second factor cannot increase formation on average. Zero-probability branches are allowed. This is the coordinate-partition instance of Vidal Theorem 2.

**Theorem 1.28 (Witness.witness_lower).**

$$\forall (\rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right)), \mathbb C\right)), \forall (w:(\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right))\to \mathbb C), ((\operatorname{Nonempty}\left(\operatorname{Ensemble}\left(\rho\right)\right))\land (\sum_{x\in (\operatorname{Fin}\left(2\right))\times (\operatorname{Fin}\left(2\right))} (\Vert w(x)\Vert^2)=1))\longrightarrow \operatorname{Analytic}.\operatorname{f}(2\cdot \operatorname{Witness}.\operatorname{W}(w,\rho))\le E_F(\rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.witness_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The new formation lower bound combines the determinant readout estimate with the convex concurrence function.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.E_F`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.Ensemble`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.S`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.W`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.branchMass`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.branchVec`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.conditionalEnsemble`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.cost_set_nonempty_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.ensembleCost`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.expectation`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.f`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.f_convex`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.formation_le_cost`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.formation_nonneg`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.lower_rational`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.marginal_trace`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.projectBlock`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.pure_qubit_le_one`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.pure_qubit_nonneg`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.qubit_entropy_concave`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.qubit_entropy_det`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.restrictVec`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.selective_formation`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.spectral_ensemble_nonempty`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.star_root_upper`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.trace_outer`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.upper_rational`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.witness_lower`
- Dependency: [D5/S3/Quantum/CloningMachine](../../CloningMachine.md)
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../StructuredNegativityCoincidenceRefutation.md)
- Dependency: [D5/S3/Quantum/Fibers/PhysicalFiber](../../Fibers/PhysicalFiber.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
