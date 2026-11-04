# Exact W-state Bell-measurement optimum

## Abstract

The W-state Bell-measurement network optimum is sqrt(13)/3.

The three tensor factors are ordered Alice, end node, Charlie. Pauli coordinates k : Fin 3 are X, Y, Z in that order. The function pauli1 is D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.pauli1; its arguments 1, 2, 3 give X, Y, Z. Central indices lie in Fin 4; index 0 is the identity and indices 1, 2, 3 select the three members of the frame. Every real coefficient is embedded in the complex scalars by Complex.ofReal. The maxima are represented by sSup.

**Definition 1.1 (The W-state conditional correlation vector).**

$$\forall (e: \operatorname{Fin}\left(3\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (\forall (f: \operatorname{Fin}\left(3\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (\forall (\mu: \operatorname{Fin}\left(4\right)), (\forall (\nu: \operatorname{Fin}\left(4\right)), (\operatorname{tau}\left(e, f, \mu, \nu\right) = (\lambda (k: \operatorname{Fin}\left(3\right))\mapsto \operatorname{let} (w: ((\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right))\times\operatorname{Fin}\left(2\right)) \to \mathbb{C}) := (\lambda (i: ((\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right))\times\operatorname{Fin}\left(2\right)))\mapsto \operatorname{if} ((i = ((0, 0), 1)) \lor ((i = ((0, 1), 0)) \lor (i = ((1, 0), 0)))) \operatorname{then} (\frac{1}{\operatorname{Complex.sqrt}\left(3\right)}: \mathbb{C}) \operatorname{else} 0); \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{Matrix.vecMulVec}\left(w, \operatorname{star}\left(w\right)\right) \cdot \operatorname{Matrix.kronecker}\left(\operatorname{Matrix.kronecker}\left((\operatorname{if} (\mu = 0) \operatorname{then} 1 \operatorname{else} \sum_{(k: \operatorname{Fin}\left(3\right))}(\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(e\left(\operatorname{if} (\mu = 0) \operatorname{then} 0 \operatorname{else} \operatorname{Fin.mk}\left(\operatorname{Nat.sub}\left(\operatorname{val}\left(\mu\right), 1\right), \operatorname{by} \operatorname{omega}\right), k\right)\right), \operatorname{pauli1}\left(\operatorname{Fin.succ}\left(k\right)\right)\right))), \operatorname{pauli1}\left(\operatorname{Fin.succ}\left(k\right)\right)\right), (\operatorname{if} (\nu = 0) \operatorname{then} 1 \operatorname{else} \sum_{(k: \operatorname{Fin}\left(3\right))}(\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(f\left(\operatorname{if} (\nu = 0) \operatorname{then} 0 \operatorname{else} \operatorname{Fin.mk}\left(\operatorname{Nat.sub}\left(\operatorname{val}\left(\nu\right), 1\right), \operatorname{by} \operatorname{omega}\right), k\right)\right), \operatorname{pauli1}\left(\operatorname{Fin.succ}\left(k\right)\right)\right)))\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.tau` (`✓ std3`).

*Citation.* Sudip Chakrabarty and Amit Kundu (2026). *Network nonlocality with tripartite entangled sources*. DOI: [10.48550/arXiv.2610.35838](https://doi.org/10.48550/arXiv.2610.35838). URL: <https://arxiv.org/abs/2610.35838v1>.

*Commentary.*

PDF page 4 defines τμν = (Tr[ρ Aμ ⊗ σₖ ⊗ Cν])ₖ₌₁,₂,₃. It states: “We write Aᵢ = eᵢ · σ and Cⱼ = fⱼ · σ, and set A₀ = C₀ = 𝕀.” For a nonzero central index μ its frame index has natural value μ.val − 1; Nat.sub denotes truncated natural subtraction. PDF page 3 defines |W⟩ = 1/√3 (|001⟩ + |010⟩ + |100⟩). Here ρ is Matrix.vecMulVec w (star w), with the displayed literal W ket w. The real part is taken after the trace.

**Definition 1.2 (Optimization over orthogonal unit directions).**

$$\forall (u: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\forall (v: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\operatorname{lambda}\left(u, v\right) = \operatorname{sSup}\left(\{(q: \mathbb{R}) | \exists (n: \operatorname{Fin}\left(3\right) \to \mathbb{R}), (\exists (n': \operatorname{Fin}\left(3\right) \to \mathbb{R}), ((\sum_{(coord: \operatorname{Fin}\left(3\right))}(n\left(coord\right)^{2}) = 1) \land ((\sum_{(coord: \operatorname{Fin}\left(3\right))}(n'\left(coord\right)^{2}) = 1) \land (((\sum_{(i: \operatorname{Fin}\left(3\right))}(n\left(i\right) \cdot n'\left(i\right))) = 0) \land (q = (\sum_{(i: \operatorname{Fin}\left(3\right))}(u\left(i\right) \cdot n\left(i\right)))^{2} + (\sum_{(i: \operatorname{Fin}\left(3\right))}(v\left(i\right) \cdot n'\left(i\right)))^{2})))))\}\right)))$$

*Formalization.* `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.lambda` (`✓ std3`).

*Citation.* Sudip Chakrabarty and Amit Kundu (2026). *Network nonlocality with tripartite entangled sources*. DOI: [10.48550/arXiv.2610.35838](https://doi.org/10.48550/arXiv.2610.35838). URL: <https://arxiv.org/abs/2610.35838v1>.

*Commentary.*

PDF page 4: “The network value therefore depends on how much of τμν and τμ′ν′ two perpendicular directions can capture. For two vectors τ, τ′ this is” Λ(τ, τ′) = max over n ⟂ n′ of (τ · n)² + (τ′ · n′)². Both directions have squared Euclidean length one. Every scalar product and squared length is displayed as its three-coordinate sum.

**Definition 1.3 (The exact optimum assertion).**

$$\operatorname{claim} \Leftrightarrow (\operatorname{Real.sqrt}\left(\operatorname{sSup}\left(\{(q: \mathbb{R}) | \exists (e: \operatorname{Fin}\left(3\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (\exists (f: \operatorname{Fin}\left(3\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), ((\operatorname{Orthonormal}\left(\mathbb{R}, e\right)) \land ((\operatorname{Orthonormal}\left(\mathbb{R}, f\right)) \land (\exists (\mu: \operatorname{Fin}\left(4\right)), (\exists (\nu: \operatorname{Fin}\left(4\right)), (\exists (\mu': \operatorname{Fin}\left(4\right)), (\exists (\nu': \operatorname{Fin}\left(4\right)), (q = \operatorname{lambda}\left(\operatorname{tau}\left(e, f, \mu, \nu\right), \operatorname{tau}\left(e, f, \mu', \nu'\right)\right)))))))))\}\right)\right) = \frac{\operatorname{Real.sqrt}\left(13\right)}{3})$$

*Formalization.* `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.claim` (`✓ std3`).

*Citation.* Sudip Chakrabarty and Amit Kundu (2026). *Network nonlocality with tripartite entangled sources*. DOI: [10.48550/arXiv.2610.35838](https://doi.org/10.48550/arXiv.2610.35838). URL: <https://arxiv.org/abs/2610.35838v1>.

*Commentary.*

PDF page 5: “For the W state, τ₃₃ = −ẑ and τ₁₃ = ⅔x̂ are orthogonal, which gives N_c ≥ √13/3 ≈ 1.202. The numerical optimization over frames finds no larger value.” Proposition 1 on PDF page 4 maximizes Λ over both orthonormal frames and all four central indices. The assertion below includes index 0 and repeated index pairs; it concerns Bell-state measurements.

**Theorem 1.4 (The exact Bell-state-measurement optimum).**

$$\operatorname{Real.sqrt}\left(\operatorname{sSup}\left(\{(q: \mathbb{R}) | \exists (e: \operatorname{Fin}\left(3\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (\exists (f: \operatorname{Fin}\left(3\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), ((\operatorname{Orthonormal}\left(\mathbb{R}, e\right)) \land ((\operatorname{Orthonormal}\left(\mathbb{R}, f\right)) \land (\exists (\mu: \operatorname{Fin}\left(4\right)), (\exists (\nu: \operatorname{Fin}\left(4\right)), (\exists (\mu': \operatorname{Fin}\left(4\right)), (\exists (\nu': \operatorname{Fin}\left(4\right)), (q = \operatorname{lambda}\left(\operatorname{tau}\left(e, f, \mu, \nu\right), \operatorname{tau}\left(e, f, \mu', \nu'\right)\right)))))))))\}\right)\right) = \frac{\operatorname{Real.sqrt}\left(13\right)}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/w-state-bsm-optimum` (proved) by `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"w-state-bsm-optimum","declaration_gid":"D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sudip Chakrabarty and Amit Kundu (2026). *Network nonlocality with tripartite entangled sources*. DOI: [10.48550/arXiv.2610.35838](https://doi.org/10.48550/arXiv.2610.35838). URL: <https://arxiv.org/abs/2610.35838v1>.

*Commentary.*

For unit a and c the W correlation T(a,c) satisfies 9‖T(a,c)‖² = (2a₀c₀ + 2a₁c₁ − a₂c₂)² + 4a₂² + 4c₂². Parseval's equality for each complete orthonormal frame bounds the selected pairs by 13/9. Identity indices give a squared length at most 4/9; identical nonidentity pairs satisfy Bessel's bound. The standard frames give τ₃₃ = −ẑ and τ₁₃ = (2/3)x̂, which are orthogonal and attain 13/9. Taking the nonnegative square root gives √13/3. This statement does not optimize over the larger product-projective class.

## References

- Truth anchor: `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.claim`
- Truth anchor: `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.lambda`
- Truth anchor: `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.result`
- Truth anchor: `D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.tau`
- Dependency: [D5/S3/Quantum/Contextuality/EightVertexQutritBound](../Contextuality/EightVertexQutritBound.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction](../QuantumChannels/HiaiRuskaiRiemannianContraction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight](../QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.md)
