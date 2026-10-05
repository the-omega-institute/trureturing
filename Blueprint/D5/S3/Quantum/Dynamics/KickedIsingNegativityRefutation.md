# A generic-state counterexample in the kicked Ising chain

## Abstract

Pathak's generic-state negativity identity fails on a four-site kicked Ising chain.

**Definition 1.1 (Ising Hamiltonian).**

$$\forall L \in \mathbb{N},\; \forall h \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \operatorname{hIsing}\left(h\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(\frac{\pi}{4}\right), \sum_{i:\operatorname{Fin}\left(L\right)}((\operatorname{localOp}\left(i, qubitZ\right)) \cdot (\operatorname{localOp}\left(\operatorname{finRotate}\left(L\right)\left(i\right), qubitZ\right)))\right) + \sum_{i:\operatorname{Fin}\left(L\right)}(\operatorname{smul}\left(\operatorname{ofReal}\left(h\left(i\right)\right), \operatorname{localOp}\left(i, qubitZ\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.hIsing` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (1), p. 1, defines H_I = J ∑ᵢ σᶻᵢσᶻᵢ₊₁ + ∑ᵢ hᵢσᶻᵢ. The source states: "We specifically consider J = π/4, b = −π/4 for our analysis." Sites use Fin L, with finRotate L as the periodic successor; ↑ and ↓ are 0 and 1. The frozen localOp embeds a qubit matrix at its site, and qubitZ is the Pauli Z matrix. Real coefficients enter ℂ through ofReal; smul is scalar multiplication.

**Definition 1.2 (Kick Hamiltonian).**

$$\forall L \in \mathbb{N},\; \operatorname{hKick}\left(L\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(\frac{0 - (\pi)}{4}\right), \sum_{i:\operatorname{Fin}\left(L\right)}(\operatorname{localOp}\left(i, qubitX\right))\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.hKick` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (1), p. 1, defines H_K = ∑ᵢ b σˣᵢ. Here b = −π/4; qubitX is the frozen Pauli X matrix.

**Definition 1.3 (Literal Floquet operator).**

$$\forall L \in \mathbb{N},\; \forall h \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \operatorname{floquet}\left(h\right) = (NormedSpace.exp\left(\operatorname{smul}\left(0 - (Complex.I), \operatorname{hKick}\left(L\right)\right)\right)) \cdot (NormedSpace.exp\left(\operatorname{smul}\left(0 - (Complex.I), \operatorname{hIsing}\left(h\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.floquet` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (2), p. 1: U = U_K U_I. The source states "where U_I = e^{−i H_I} and U_K = e^{−i H_K}." The matrix exponentials are NormedSpace.exp, and I in Complex.I denotes the imaginary unit.

**Definition 1.4 (Initial product state).**

$$\forall L \in \mathbb{N},\; \forall theta \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall phi \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall x \in \operatorname{Fin}\left(L\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{initial}\left(theta, phi\right)\left(x\right) = \prod_{i:\operatorname{Fin}\left(L\right)}(\operatorname{ite}\left(x\left(i\right) = 0, \operatorname{ofReal}\left(Real.cos\left(\frac{theta\left(i\right)}{2}\right)\right), (Complex.exp\left((Complex.I) \cdot (\operatorname{ofReal}\left(phi\left(i\right)\right))\right)) \cdot (\operatorname{ofReal}\left(Real.sin\left(\frac{theta\left(i\right)}{2}\right)\right))\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.initial` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (3), pp. 1–2: |ψ_{θ,φ}⟩ = ⊗ₖ (cos(θₖ/2)|↑⟩ + e^{iφₖ}sin(θₖ/2)|↓⟩). The formula displays the computational-basis amplitude at x. The letters theta and phi encode the Lean parameters θ and φ. All trigonometric arguments are real, and their values are embedded in ℂ by ofReal. The conditional ite(c,a,b) selects a when c holds and b otherwise.

**Definition 1.5 (Generic states).**

$$\forall L \in \mathbb{N},\; \forall theta \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \operatorname{generic}\left(theta\right) \Leftrightarrow ((\neg (\forall i \in \operatorname{Fin}\left(L\right),\; theta\left(i\right) = \frac{\pi}{2})) \land (\neg (\forall i \in \operatorname{Fin}\left(L\right),\; (theta\left(i\right) = 0) \lor (theta\left(i\right) = \pi))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.generic` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Page 2 states verbatim: "States which do not belong to these class will henceforth be called generic." Equation (4) defines the transverse class by θₖ = π/2 for every site and the longitudinal class by θₖ ∈ {0,π} for every site. Thus generic excludes both classes, rather than imposing randomness or a measure-theoretic qualifier.

**Definition 1.6 (Half-order Rényi entropy).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall rho \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{renyiHalf}\left(rho\right) = (2) \cdot (Real.log\left(Complex.re\left(Matrix.trace\left(\operatorname{cfc}\left(Real.sqrt, rho\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.renyiHalf` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (9), p. 2, defines S_A^(α) = (1/(1−α)) log(tr(ρ_A^α)). At α = 1/2 this is twice the logarithm of the trace of the matrix square root. For density matrices cfc Real.sqrt is precisely that square root, and the trace is real. The real part makes the ℝ-valued expression explicit. On non-Hermitian inputs the real continuous functional calculus is zero. Anonymous bracket entries record the Lean typeclass arguments.

**Definition 1.7 (Contiguous cyclic tripartition).**

$$\forall L \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \operatorname{contiguous}\left(A, B, C\right) \Leftrightarrow (\exists o \in \mathbb{N},\; \exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; (0 < a) \land ((a < b) \land ((b < L) \land ((A = Finset.filter\left((i:\operatorname{Fin}\left(L\right)) \mapsto \operatorname{val}\left(\left((\operatorname{finRotate}\left(L\right))^{o}\right)\left(i\right)\right) < a, Finset.univ\right)) \land ((B = Finset.filter\left((i:\operatorname{Fin}\left(L\right)) \mapsto (a \le \operatorname{val}\left(\left((\operatorname{finRotate}\left(L\right))^{o}\right)\left(i\right)\right)) \land (\operatorname{val}\left(\left((\operatorname{finRotate}\left(L\right))^{o}\right)\left(i\right)\right) < b), Finset.univ\right)) \land (C = Finset.filter\left((i:\operatorname{Fin}\left(L\right)) \mapsto b \le \operatorname{val}\left(\left((\operatorname{finRotate}\left(L\right))^{o}\right)\left(i\right)\right), Finset.univ\right)))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.contiguous` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Page 2 states: "In the following we now consider a tri-partition of state ABC with subsystem size L_A,L_B and L_C." The periodic chain is cut at a and b after a rotation by o. The three blocks are nonempty and disjoint and exhaust the sites. The val function extracts the natural value of a Fin index; the exponent o is a natural permutation power.

**Definition 1.8 (Join subsystem coordinates).**

$$\forall L \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall x \in \operatorname{Subtype}\left((i:\operatorname{Fin}\left(L\right)) \mapsto i \in A\right) \to \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Subtype}\left((i:\operatorname{Fin}\left(L\right)) \mapsto i \in B\right) \to \operatorname{Fin}\left(2\right),\; \forall z \in \operatorname{Outside}\left(A \cup B\right) \to \operatorname{Fin}\left(2\right),\; \forall i \in \operatorname{Fin}\left(L\right),\; \operatorname{joinParts}\left(A, B, x, y, z\right)\left(i\right) = \operatorname{dite}\left(i \in A, (hA:i \in A) \mapsto x\left(Subtype.mk\left(i, \mathit{hA}\right)\right), (hA:\neg i \in A) \mapsto \operatorname{dite}\left(i \in B, (hB:i \in B) \mapsto y\left(Subtype.mk\left(i, hB\right)\right), (hB:\neg i \in B) \mapsto z\left(Subtype.mk\left(i, Finset.notMem_{union}.mpr\left(\langle\mathit{hA}, hB\rangle\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.joinParts` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

The coordinates x, y and z lie on A, B and the complement of A ∪ B. The dependent conditional dite supplies membership proofs hA and hB to Subtype.mk. In the final branch hA and hB are nonmembership hypotheses, and Finset.notMem_union.mpr ⟨hA, hB⟩ proves membership in the complement. Outside is the frozen complement subtype. On disjoint blocks these assignments combine to one chain configuration, as used in the partial-trace expression on p. 2.

**Definition 1.9 (Joint reduced density matrix).**

$$\forall L \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall psi \in \left(\operatorname{Fin}\left(L\right) \to \operatorname{Fin}\left(2\right)\right) \to \mathbb{C},\; \operatorname{reducedAB}\left(A, B, psi\right) = \operatorname{partialTraceRight}\left(Matrix.vecMulVec\left((p:((\operatorname{Subtype}\left((i:\operatorname{Fin}\left(L\right)) \mapsto i \in A\right) \to \operatorname{Fin}\left(2\right))\times(\operatorname{Subtype}\left((i:\operatorname{Fin}\left(L\right)) \mapsto i \in B\right) \to \operatorname{Fin}\left(2\right)))\times(\operatorname{Outside}\left(A \cup B\right) \to \operatorname{Fin}\left(2\right))) \mapsto psi\left(\operatorname{joinParts}\left(A, B, \operatorname{fst}\left(\operatorname{fst}\left(p\right)\right), \operatorname{snd}\left(\operatorname{fst}\left(p\right)\right), \operatorname{snd}\left(p\right)\right)\right), \operatorname{star}\left((p:((\operatorname{Subtype}\left((i:\operatorname{Fin}\left(L\right)) \mapsto i \in A\right) \to \operatorname{Fin}\left(2\right))\times(\operatorname{Subtype}\left((i:\operatorname{Fin}\left(L\right)) \mapsto i \in B\right) \to \operatorname{Fin}\left(2\right)))\times(\operatorname{Outside}\left(A \cup B\right) \to \operatorname{Fin}\left(2\right))) \mapsto psi\left(\operatorname{joinParts}\left(A, B, \operatorname{fst}\left(\operatorname{fst}\left(p\right)\right), \operatorname{snd}\left(\operatorname{fst}\left(p\right)\right), \operatorname{snd}\left(p\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.reducedAB` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Page 2 defines ρ_AB(t) = tr_C(|ψ(t)⟩⟨ψ(t)|). The coordinate function inside vecMulVec is the same ψ expressed on the product of the retained blocks and the complement. Its star is complex conjugation, so vecMulVec forms the rank-one density matrix. The frozen partialTraceRight sums over the complement.

**Definition 1.10 (Partial transposition).**

$$\forall A \in Type,\; \forall B \in Type,\; \forall rho \in \operatorname{Matrix}\left((A)\times(B), (A)\times(B), \mathbb{C}\right),\; \forall p \in (A)\times(B),\; \forall q \in (A)\times(B),\; \operatorname{partialTranspose}\left(rho\right)\left(p, q\right) = rho\left((\operatorname{fst}\left(p\right),\operatorname{snd}\left(q\right)), (\operatorname{fst}\left(q\right),\operatorname{snd}\left(p\right))\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (5), p. 2, uses partial transposition with respect to B. It swaps the two B indices while preserving the A indices. This definition allows different subsystem dimensions; the existing partialTransposeB is used directly for the equal two-qubit matrix in the proof.

**Definition 1.11 (Integer-time evolution).**

$$\forall L \in \mathbb{N},\; \forall h \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall theta \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall phi \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall t \in \mathbb{Z},\; \operatorname{evolved}\left(h, theta, phi, t\right) = Matrix.mulVec\left((\operatorname{floquet}\left(h\right))^{t}, \operatorname{initial}\left(theta, phi\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.evolved` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

The source evolves the initial state with U_KI[h]^t (supplement, p. 6). The exponent is an integer power of the literal Floquet matrix, and Matrix.mulVec is its action on the amplitude vector. The counterexample uses t = 1.

**Definition 1.12 (Logarithmic negativity).**

$$\forall A \in Type,\; \forall B \in Type,\; [\operatorname{Fintype}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{DecidableEq}\left(B\right)] \forall rho \in \operatorname{Matrix}\left((A)\times(B), (A)\times(B), \mathbb{C}\right),\; \operatorname{logNegativity}\left(rho\right) = Real.log\left(\operatorname{traceNorm}\left(\operatorname{partialTranspose}\left(rho\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.logNegativity` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (5), p. 2: 𝓔(t) = ln tr(√((ρ_AB^{T_B}(t))†ρ_AB^{T_B}(t))). The frozen traceNorm is defined by precisely this trace-of-square-root expression, with conjTranspose as the adjoint. Real.log is the natural logarithm.

**Definition 1.13 (Half-order Rényi mutual information).**

$$\forall A \in Type,\; \forall B \in Type,\; [\operatorname{Fintype}\left(A\right)] [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{DecidableEq}\left(B\right)] \forall rho \in \operatorname{Matrix}\left((A)\times(B), (A)\times(B), \mathbb{C}\right),\; \operatorname{mutualHalf}\left(rho\right) = \operatorname{renyiHalf}\left(\operatorname{partialTraceRight}\left(rho\right)\right) + \operatorname{renyiHalf}\left(\operatorname{partialTraceLeft}\left(rho\right)\right) - \operatorname{renyiHalf}\left(rho\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.mutualHalf` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Equation (9), p. 2: I_{A:B}^(α)(t) = S_A^(α)(t) + S_B^(α)(t) − S_AB^(α)(t). Here α = 1/2, partialTraceRight retains A and partialTraceLeft retains B.

**Definition 1.14 (Pathak's Conjecture 1 at half order).**

$$claim \Leftrightarrow (\forall L \in \mathbb{N},\; \forall h \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall theta \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall phi \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right),\; \forall t \in \mathbb{Z},\; (\operatorname{contiguous}\left(A, B, C\right)) \Rightarrow ((\operatorname{generic}\left(theta\right)) \Rightarrow ((2) \cdot (\operatorname{logNegativity}\left(\operatorname{reducedAB}\left(A, B, \operatorname{evolved}\left(h, theta, phi, t\right)\right)\right)) = \operatorname{mutualHalf}\left(\operatorname{reducedAB}\left(A, B, \operatorname{evolved}\left(h, theta, phi, t\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.claim` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Conjecture 1, p. 3, states verbatim: "2𝓔(t) = I_{A:B}^{(α)}(t), hold for generic states at all times t." This is its α = 1/2 specialization, quantified over the chain length, real fields, product-state angles, contiguous tripartition and integer time. Each allowed tripartition has nonempty blocks. The specific fields are hᵢ = 1, with phases φᵢ = 0, for the counterexample.

**Theorem 1.15 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/pathak-2026-kicked-ising-negativity-refutation` (refuted) by `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pathak-2026-kicked-ising-negativity-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

Take L = 4, A = {0}, B = {1}, C = {2,3}, t = 1, hᵢ = 1 and φᵢ = 0. The initial state is |+⟩|+⟩|r⟩|r⟩, where |r⟩ = (2|0⟩+|1⟩)/√5, encoded by θ = (π/2,π/2,2 arctan(1/2),2 arctan(1/2)). It is generic. Factoring the commuting kick exponentials and the diagonal Ising exponential gives U = −W^{⊗4}G, with W a single-qubit unitary and G the periodic product of controlled-Z gates. The local unitaries preserve both measures. Before their action, the reduced density matrix has spectrum {16/25,4/25,4/25,1/25}; its partial transpose has spectrum {23/50,17/50,17/50,−7/50}, and both marginals are 1/2 times the identity. Hence 2𝓔(1) = log(1024/625) and I_{A:B}^(1/2)(1) = log(100/81). Strict injectivity of the logarithm on positive reals and the unequal rational arguments contradict the asserted equality. These finite-chain values do not settle a thermodynamic-limit identity at early times.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.contiguous`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.evolved`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.floquet`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.generic`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.hIsing`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.hKick`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.initial`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.joinParts`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.logNegativity`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.mutualHalf`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.reducedAB`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.renyiHalf`
- Truth anchor: `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation](../Entanglement/FourQubitResidualSumMonotoneRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../Entanglement/StructuredNegativityCoincidenceRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
