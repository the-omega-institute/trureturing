# All qubit maximizers of the imaginary Bargmann invariant

## Abstract

For every n at least three, the unit qubit tuples with imaginary Bargmann invariant tau n form one unitary orbit of a latitude polygon, allowing an independent phase at each vertex.

Vectors have type Fin 2 → ℂ. For a unit vector v, Matrix.vecMulVec v (star v) is its rank-one projector. Indices have type Fin n and start at zero. List.ofFn lists the outer products in increasing index order and List.prod takes their ordered matrix product. Real division, the real square root and natural powers have Lean's total meanings; the exponent n − 1 is natural subtraction, whereas the denominator 2 · (n − 1) uses real subtraction after coercing n to ℝ.

**Definition 1.1 (Ordered trace of pure states).**

$$\forall (n : \mathbb{N}), \forall (\psi : (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{C}))), \operatorname{bargmann}\left(\psi\right) = \operatorname{Matrix.trace}\left(\operatorname{List.prod}\left(\operatorname{List.ofFn}\left(\operatorname{fun} (j : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Matrix.vecMulVec}\left(\psi\left(j\right), \operatorname{star}\left(\psi\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.bargmann` (`✓ std3`).

*Citation.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Zhang and Xie, Definition 3.1, p. 9: “The so-called nth-order Bargmann invariant for such n-tuple Ψ = (ρ₁, …, ρₙ) is defined as Δₙ(Ψ) := Tr(ρ₁ ⋯ ρₙ).” Section 2, p. 4: “Unit vector |ψ⟩ in ℂ^d will be called wave functions and its ranked-one projector ψ ≡ |ψ⟩⟨ψ| will be called pure state.” Here d = 2 and each ρ is the displayed outer product of its amplitude vector with its conjugate.

**Definition 1.2 (The maximal imaginary value).**

$$\forall (n : \mathbb{N}), \operatorname{tau}\left(n\right) = \frac{\operatorname{Real.cos}\left(\frac{\operatorname{Real.pi}}{(n : \mathbb{R})}\right)^{n}}{\operatorname{Real.cos}\left(\frac{\operatorname{Real.pi}}{2 \cdot ((n : \mathbb{R}) - 1)}\right)^{(n - 1)}}$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.tau` (`✓ std3`).

*Citation.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Zhang and Xie, Corollary 5.5, p. 25, Eq. (5.15): “τₙ := cosⁿ(π/n) secⁿ⁻¹(π/[2(n−1)]).” The reciprocal cosine power expresses the secant power; the classification below concerns n ≥ 3.

**Definition 1.3 (The latitude polygon).**

$$\forall (n : \mathbb{N}), \forall (j : \operatorname{Fin}\left(n\right)), \operatorname{let} (t : \mathbb{R}) := \frac{1 - \frac{\operatorname{Real.tan}\left(\frac{\operatorname{Real.pi}}{2 \cdot ((n : \mathbb{R}) - 1)}\right)}{\operatorname{Real.tan}\left(\frac{\operatorname{Real.pi}}{(n : \mathbb{R})}\right)}}{2}; \operatorname{maximizer}\left(n, j\right) = ![(\operatorname{Real.sqrt}\left(1 - t\right) : \mathbb{C}), (\operatorname{Real.sqrt}\left(t\right) : \mathbb{C}) \cdot \operatorname{Complex.exp}\left(\frac{2 \cdot (\operatorname{Real.pi} : \mathbb{C}) \cdot \operatorname{Complex.I} \cdot (\operatorname{val}\left(j\right) : \mathbb{C})}{(n : \mathbb{C})}\right)]$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.maximizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

The jth vector is (√(1 − t), √t · exp(2πij/n)), with t = (1 − tan(π/[2(n−1)])/tan(π/n))/2. The square roots are embedded from ℝ into ℂ. For n ≥ 3 the weight t lies strictly between zero and one half. The last coordinate uses the complex coercions of j and n.

**Definition 1.4 (The complete set of maximizing tuples).**

$$\operatorname{claim} = (\forall (n : \mathbb{N}), (3 \le n) \Rightarrow (\forall (\psi : (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{C}))), (\forall (j : \operatorname{Fin}\left(n\right)), \operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(j\right)\right), \psi\left(j\right)\right) = 1) \Rightarrow ((\operatorname{Complex.im}\left(\operatorname{bargmann}\left(\psi\right)\right) = \operatorname{tau}\left(n\right)) \Leftrightarrow (\exists (U : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land (\exists (eta : (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\forall (j : \operatorname{Fin}\left(n\right)), \left\lVert eta\left(j\right) \right\rVert = 1) \land (\forall (j : \operatorname{Fin}\left(n\right)), \psi\left(j\right) = \operatorname{SMul.smul}\left(eta\left(j\right), \operatorname{Matrix.mulVec}\left(U, \operatorname{maximizer}\left(n, j\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Zhang and Xie, p. 26: “The quantity τ_n predicts the upper bound for the imaginary part of any nth-order Bargmann invariant. This immediately raises the question: what is the complete set of n-tuples Ψ = (|ψ_1⟩, …, |ψ_n⟩) in ℂ² that achieve Im Tr(ψ_1 … ψ_n) = τ_n? We leave this characterization, along with the operational interpretation of the condition z ∈ 𝓑_{n+1} ∖ 𝓑_n, as interesting open problems for future work.” The displayed answer uses one common matrix U in Matrix.unitaryGroup and independent complex phases eta of norm one. The wave-function premise is star (Ψ j) dotProduct (Ψ j) = 1. The second question is outside this equivalence.

**Theorem 1.5 (Classification of every maximizing qubit tuple).**

$$\forall (n : \mathbb{N}), (3 \le n) \Rightarrow (\forall (\psi : (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{C}))), (\forall (j : \operatorname{Fin}\left(n\right)), \operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(j\right)\right), \psi\left(j\right)\right) = 1) \Rightarrow ((\operatorname{Complex.im}\left(\operatorname{bargmann}\left(\psi\right)\right) = \operatorname{tau}\left(n\right)) \Leftrightarrow (\exists (U : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land (\exists (eta : (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\forall (j : \operatorname{Fin}\left(n\right)), \left\lVert eta\left(j\right) \right\rVert = 1) \land (\forall (j : \operatorname{Fin}\left(n\right)), \psi\left(j\right) = \operatorname{SMul.smul}\left(eta\left(j\right), \operatorname{Matrix.mulVec}\left(U, \operatorname{maximizer}\left(n, j\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-xie-2026-bargmann-imaginary-maximizers` (proved) by `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-xie-2026-bargmann-imaginary-maximizers","declaration_gid":"D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Rephase consecutive overlaps onto one ray. AM–GM compares their product with their mean, and the exposed edge of the regular polygon of Fourier phases bounds that mean. Equality at the unique scalar maximum removes every Fourier mode except zero and one. Parseval's energy identity and unit length at two vertices force these two modes to be orthogonal. Their Gram matrix determines a common unitary, and the mean overlap fixes the latitude weight. Conversely, the polygon has constant consecutive overlap and its ordered trace has imaginary part tau n; unitary transformations and the individual phases preserve that trace.

## References

- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.bargmann`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.claim`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.maximizer`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.tau`
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](../Algebra/GramUnitaryExtension.md)
