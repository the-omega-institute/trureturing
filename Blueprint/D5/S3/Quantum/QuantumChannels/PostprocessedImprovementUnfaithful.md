# Biased post-processed improvements are not faithful

## Abstract

Every biased prior admits a coherence-creating qubit channel with zero post-processed improvement.

Matrices have complex entries. MatrixMap(Fin a, Fin b, ℂ) is the space of complex linear maps from a by a matrices to b by b matrices. IsChannel means completely positive and trace preserving, traceNorm is the matrix trace norm, and LinearMap.comp applies its second argument first. The prior l is real, and the complementary prior is 1 − l.

**Definition 1.1 (Full dephasing).**

$$\forall (n: \mathbb{N}), ((\operatorname{dephase}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)) = \operatorname{LinearMap.comp}\left(\operatorname{Matrix.diagonalLinearMap}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \mathbb{C}\right), \operatorname{Matrix.diagLinearMap}\left(\operatorname{Fin}\left(n\right), \mathbb{C}, \mathbb{C}\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.dephase` (`✓ std3`).

*Citation.* Michele Masini; Thomas Theurer; Martin B. Plenio (2021). *Coherence of operations and interferometry*. DOI: [10.1103/PhysRevA.103.042426](https://doi.org/10.1103/PhysRevA.103.042426). URL: <https://arxiv.org/abs/2102.04863v2>.

*Commentary.*

Full dephasing extracts the diagonal of a matrix and puts it back into a diagonal matrix. It removes precisely the off-diagonal entries in the coordinate basis. This is the operation Δ in Section II A of Masini, Theurer and Plenio (arXiv:2102.04863v2, TeX lines 111–115). The definition permits every natural dimension n.

**Definition 1.2 (Maximally incoherent operations).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (\psi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), ((\operatorname{IsMIO}\left(\psi\right)) \Leftrightarrow ((\operatorname{IsChannel}\left(\psi\right)) \land (\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right)), (\psi\left(\operatorname{dephase}\left(x\right)\right) = \operatorname{dephase}\left(\psi\left(\operatorname{dephase}\left(x\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.IsMIO` (`✓ std3`).

*Citation.* Michele Masini; Thomas Theurer; Martin B. Plenio (2021). *Coherence of operations and interferometry*. DOI: [10.1103/PhysRevA.103.042426](https://doi.org/10.1103/PhysRevA.103.042426). URL: <https://arxiv.org/abs/2102.04863v2>.

*Commentary.*

A maximally incoherent operation is a channel whose output is diagonal whenever its input has been dephased. The identity is required for every complex input matrix x, and includes both the channel condition and preservation of diagonality. It restates ΨΔ = ΔΨΔ from Section II A (TeX lines 132–134).

**Definition 1.3 (The diagonal phase channel).**

$$\forall (m: \mathbb{N}), (\forall (\phi: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), ((\operatorname{phaseChannel}\left(\phi\right): \operatorname{MatrixMap}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)) = \operatorname{MatrixMap.conj}\left(\operatorname{Matrix.diagonal}\left((\lambda (i: \operatorname{Fin}\left(m\right)) \mapsto (\operatorname{Complex.exp}\left(\operatorname{Complex.ofReal}\left(\phi\left(i\right)\right) \cdot \operatorname{Complex.I}\right)))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.phaseChannel` (`✓ std3`).

*Citation.* Michele Masini; Thomas Theurer; Martin B. Plenio (2021). *Coherence of operations and interferometry*. DOI: [10.1103/PhysRevA.103.042426](https://doi.org/10.1103/PhysRevA.103.042426). URL: <https://arxiv.org/abs/2102.04863v2>.

*Commentary.*

For a real phase function φ on Fin m, conjugate by the diagonal matrix with entries exp(iφ(i)). MatrixMap.conj sends a matrix A to UAU† for the displayed diagonal U. The inclusion Complex.ofReal places each real phase in ℂ before multiplication by Complex.I and exponentiation. This is Λ in Section III (TeX lines 171–175).

**Definition 1.4 (The induced trace norm).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (f: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), ((\operatorname{inducedTraceNorm}\left(f\right): \mathbb{R}) = \operatorname{sSup}\left(\{r: \mathbb{R} \mid (\exists (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right)), ((\operatorname{traceNorm}\left(x\right) \le (1: \mathbb{R})) \land (\operatorname{traceNorm}\left(f\left(x\right)\right) = r)))\}\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.inducedTraceNorm` (`✓ std3`).

*Citation.* Michele Masini; Thomas Theurer; Martin B. Plenio (2021). *Coherence of operations and interferometry*. DOI: [10.1103/PhysRevA.103.042426](https://doi.org/10.1103/PhysRevA.103.042426). URL: <https://arxiv.org/abs/2102.04863v2>.

*Commentary.*

Take the real supremum of the trace norms of f(x) over the full complex matrix unit ball traceNorm(x) ≤ 1. The inputs are arbitrary complex matrices, without a positivity or Hermiticity restriction. This is the induced trace norm used in Section III A (TeX line 202). The definition applies to every complex linear map f and all natural input and output dimensions; sSup is the total real supremum operation.

**Definition 1.5 (The optimized post-processed improvement).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (l: \mathbb{R}), (\forall (\phi: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), (\forall (\theta: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), ((\operatorname{postImprovement}\left(l, \phi, \theta\right): \mathbb{R}) = (\operatorname{sSup}\left(\{r: \mathbb{R} \mid (\exists (\psi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)), ((\operatorname{IsMIO}\left(\psi\right)) \land (\operatorname{inducedTraceNorm}\left(\operatorname{LinearMap.comp}\left(\operatorname{LinearMap.comp}\left(((\operatorname{Complex.ofReal}\left(l\right)) \cdot ((\operatorname{LinearMap.id}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)))) - ((\operatorname{Complex.ofReal}\left(((1: \mathbb{R})) - (l)\right)) \cdot (\operatorname{phaseChannel}\left(\phi\right))), \psi\right), \operatorname{LinearMap.comp}\left(\theta, \operatorname{dephase}\right)\right)\right) = r)))\}\right)) - (\left|(l) - (((1: \mathbb{R})) - (l))\right|)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.postImprovement` (`✓ std3`).

*Citation.* Michele Masini; Thomas Theurer; Martin B. Plenio (2021). *Coherence of operations and interferometry*. DOI: [10.1103/PhysRevA.103.042426](https://doi.org/10.1103/PhysRevA.103.042426). URL: <https://arxiv.org/abs/2102.04863v2>.

*Commentary.*

For θ from dimension a to dimension b, optimize the induced trace norm over all maximally incoherent maps ψ from dimension b to the phase dimension m. First dephase, then apply θ, then ψ, and finally the weighted difference between the identity and the phase channel. Subtract the prior-only advantage |l − (1 − l)|. This restates Equation (14) (TeX line 273), using a real supremum in place of the maximum. Both weights are explicitly included in ℂ, with 1 − l formed in ℝ before inclusion. The definition itself allows arbitrary natural dimensions and real l; the theorem imposes the probability and nonempty-output conditions it uses.

**Theorem 1.6 (A coherent qubit channel invisible to every biased game).**

$$\forall (l: \mathbb{R}), (((0: \mathbb{R}) \le l) \to ((l \le (1: \mathbb{R})) \to ((l \ne \frac{(1: \mathbb{R})}{(2: \mathbb{R})}) \to (\forall (m: \mathbb{N}), (((1: \mathbb{N}) \le m) \to (\forall (\phi: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), (\exists (\theta: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((\operatorname{IsChannel}\left(\theta\right)) \land ((\neg (\operatorname{IsMIO}\left(\theta\right))) \land (\operatorname{postImprovement}\left(l, \phi, \theta\right) = (0: \mathbb{R})))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.result` (`✓ std3`). ∎

*Resolves.* `Problems/masini-theurer-plenio-2021-postprocessed-improvement-unfaithfulness` (proved) by `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"masini-theurer-plenio-2021-postprocessed-improvement-unfaithfulness","declaration_gid":"D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michele Masini; Thomas Theurer; Martin B. Plenio (2021). *Coherence of operations and interferometry*. DOI: [10.1103/PhysRevA.103.042426](https://doi.org/10.1103/PhysRevA.103.042426). URL: <https://arxiv.org/abs/2102.04863v2>.

*Commentary.*

First fix a phase function φ and put U = diag(exp(iφ(i))). Each diagonal entry has unit modulus. Computing the entries of UAU† shows that the phase channel preserves trace, preserves positive semidefiniteness, and fixes every diagonal matrix.

Suppose 0 ≤ l ≤ 1, d is diagonal, and d + e and d − e are positive semidefinite. Set f = l e − (1 − l)UeU†. Then d + f is the sum l(d + e) + (1 − l)U(d − e)U†, and d − f is l(d − e) + (1 − l)U(d + e)U†. Nonnegative scalar multiplication, addition and unitary conjugation preserve positivity, so both d + f and d − f are positive semidefinite.

Assume also d ≥ 0, tr(d) = 1, tr(e) = 0 and 0 ≤ t ≤ |2l − 1|. Trace preservation gives tr(f) = 0, so H = (2l − 1)d + t f has trace 2l − 1. When 2l − 1 ≥ 0, write H = (2l − 1 − t)d + t(d + f), a positive semidefinite sum. When 2l − 1 ≤ 0, write −H = (−(2l − 1) − t)d + t(d − f), also positive semidefinite. The trace norm of a positive semidefinite matrix equals its trace, and negation does not change the trace norm. Thus traceNorm(H) = |2l − 1| in both cases.

For qubits let d₀ = I₂/2 and e₀ = X/2, where X has zero diagonal and both off-diagonal entries equal to one. For s equal to 1 or −1, d₀ + s e₀ is one half of vv† with v = (1,s), hence is positive semidefinite. For any positive semidefinite ρ with trace one, the map A ↦ tr(A)ρ is a channel: its Choi matrix is ρ ⊗ I, which is positive semidefinite, and its output trace is tr(A).

Now take any maximally incoherent ψ from the qubit to dimension m. Put d = ψ(d₀) and e = ψ(e₀). The matrix d₀ is diagonal, so the defining identity of IsMIO makes d diagonal. Positivity of ψ gives d ≥ 0 and d ± e ≥ 0; trace preservation gives tr(d) = 1 and tr(e) = 0. These are exactly the conditions in the preceding norm calculation.

For 0 ≤ t ≤ 1, the matrix ρₜ = d₀ + t e₀ has diagonal entries 1/2 and off-diagonal entries t/2. It is the convex combination of d₀ + e₀ and d₀ − e₀ with weights (1 + t)/2 and (1 − t)/2, and its trace is one. Consequently Θₜ(A) = tr(A)ρₜ is a channel. If t ≠ 0 it is not maximally incoherent: applying it to the diagonal matrix |0⟩⟨0| gives ρₜ, whose (0,1) entry t/2 is nonzero.

To compute the induced norm on all complex matrices, first prove |tr(A)| ≤ traceNorm(A). A zero trace gives the inequality by nonnegativity. Otherwise set c = conjugate(tr(A))/|tr(A)|. The diagonal matrix cI is unitary and Re tr(cA) = |tr(A)|. The variational formula expressing traceNorm(A) as the maximum real trace over left multiplication by unitaries gives the inequality. It follows that, for any output matrix h and input dimension a ≥ 1, the map A ↦ tr(A)h has induced trace norm traceNorm(h): scalar homogeneity and the trace inequality give the upper bound on the unit ball, while the diagonal projector onto coordinate zero has trace and trace norm one and attains it.

For 0 ≤ l ≤ 1 set δ = |2l − 1| and t = δ/2. For each maximally incoherent ψ, use d = ψ(d₀), e = ψ(e₀) and f = l e − (1 − l)UeU† as above. The phase channel fixes ψ(I₂), since it fixes ψ(I₂/2) and the nonzero scalar 1/2 can be cancelled. Dephasing preserves the input trace. Expanding ρₜ and the compositions therefore identifies the map in the optimization with A ↦ tr(A)H, where H = (2l − 1)d + t f. Since 0 ≤ t ≤ δ, its induced trace norm is traceNorm(H) = δ for every such ψ.

When m ≥ 1, sending A to tr(A)|0⟩⟨0| in dimension m gives a maximally incoherent post-processing: it is a channel and both sides of its dephasing identity equal the same scalar multiple of the diagonal projector. The set of norm values in the optimization is therefore the singleton {δ}. Its real supremum is δ, and l − (1 − l) = 2l − 1, so postImprovement(l,φ,Θₜ) = δ − δ = 0.

Finally, l ≠ 1/2 implies δ ≠ 0 and t ≠ 0, while 0 ≤ l ≤ 1 gives δ ≤ 1 and hence 0 ≤ t ≤ 1. Thus Θₜ is a qubit channel that is not maximally incoherent and has zero optimized improvement. This proves failure of faithfulness for every biased prior, every positive phase dimension and every phase function, answering the faithfulness part of the question in Section IV (TeX line 300). The construction includes the endpoint priors and requires no separation between the phases.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.IsMIO`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.dephase`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.inducedTraceNorm`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.phaseChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.postImprovement`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.result`
- Dependency: [D5/S3/Quantum/Algebra/Unitary/BalancedUnitarySum](../Algebra/Unitary/BalancedUnitarySum.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue](EntanglementAssistedCommunicationValue.md)
- Dependency: [D5/S3/Quantum/Schatten/TraceNorm](../Schatten/TraceNorm.md)
