# A matrix refutation of the C*-algebraic Novak conjecture

## Abstract

Three self-adjoint matrices in Matrix (Fin 2) (Fin 2) complex numbers refute Krishna's C*-algebraic Novak conjecture. Their differences have scalar squares, and the exponential series gives cosine values 1, 1 and -1. The associated left-linear quadratic form takes the value -2 times the identity.

**Definition 1.1 (C*-algebraic cosine).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)] [\operatorname{NormedAlgebra}\left(\mathbb{C}, A\right)] \forall x \in A,\; \operatorname{ncos}\left(x\right) = (2: \mathbb{C})^{-1} \cdot (\operatorname{NormedSpace}.\operatorname{exp}\left(\operatorname{Complex}.\operatorname{I} \cdot (x)\right) + \operatorname{NormedSpace}.\operatorname{exp}\left(-(\operatorname{Complex}.\operatorname{I} \cdot (x))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarNovak.ncos` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2021). *C*-algebraic Schur product theorem, Pólya-Szegő-Rudin question and Novak's conjecture*. DOI: [10.48550/arXiv.2108.06662](https://doi.org/10.48550/arXiv.2108.06662). URL: <https://arxiv.org/abs/2108.06662v1>.

*Commentary.*

Definition 4.1 (arXiv:2108.06662v1, p. 9): “Define the C*-algebraic cosine function by cos: 𝒜 ∋ x ↦ cos x ≔ (eⁱˣ + e⁻ⁱˣ)/2 ∈ 𝒜.” Here ncos uses NormedSpace.exp, the exponential power series ∑ xⁿ/n!. Multiplication by the complex inverse of 2 is scalar multiplication; this definition also makes sense on a complex normed algebra before imposing completeness.

**Definition 1.2 (Ordered cosine-product entries).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{CStarAlgebra}\left(A\right)] \forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(d\right) \to A\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \forall k \in \operatorname{Fin}\left(n\right),\; \operatorname{novakEntry}\left(n, d, x, j, k\right) = \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left((\operatorname{fun} (l: \operatorname{Fin}\left(d\right)) \mapsto (2: \mathbb{C})^{-1} \cdot (1 + \operatorname{ncos}\left(x\left(j, l\right) - x\left(k, l\right)\right)))\right)\right) - (n: \mathbb{C})^{-1} \cdot ((1: A))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarNovak.novakEntry` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2021). *C*-algebraic Schur product theorem, Pólya-Szegő-Rudin question and Novak's conjecture*. DOI: [10.48550/arXiv.2108.06662](https://doi.org/10.48550/arXiv.2108.06662). URL: <https://arxiv.org/abs/2108.06662v1>.

*Commentary.*

The entry in Conjecture 4.3 (p. 10) is ∏_{l=1}^{d} (1+cos (x_{j,l}-x_{k,l}))/2-1/n. List.ofFn enumerates Fin d in increasing order, and List.prod preserves that order. Fin n and Fin d correspond to the source's indices by adding one. The subtraction uses (n : ℂ)⁻¹ acting on the algebra identity; each centered difference uses ncos.

**Definition 1.3 (The source's matrix positivity).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] \forall n \in \mathbb{N},\; \forall M \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to A\right),\; \operatorname{IsPositiveMatrix}\left(M\right) \Leftrightarrow ((\forall j \in \operatorname{Fin}\left(n\right),\; \forall k \in \operatorname{Fin}\left(n\right),\; \operatorname{star}\left(M\left(j, k\right)\right) = M\left(k, j\right)) \land (\forall v \in \operatorname{Fin}\left(n\right) \to A,\; 0 \le \sum_{j: \operatorname{Fin}\left(n\right)} \sum_{k: \operatorname{Fin}\left(n\right)} M\left(j, k\right) v\left(k\right) \operatorname{star}\left(v\left(j\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarNovak.IsPositiveMatrix` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2021). *C*-algebraic Schur product theorem, Pólya-Szegő-Rudin question and Novak's conjecture*. DOI: [10.48550/arXiv.2108.06662](https://doi.org/10.48550/arXiv.2108.06662). URL: <https://arxiv.org/abs/2108.06662v1>.

*Commentary.*

Section 2 (p. 4): “Similar to the scalar case, A ≔ [a_{j,k}]_{1≤j,k≤n} ∈ Mₙ(𝒜) is said to be positive if it is self-adjoint and ⟨Ax, x⟩ ≥ 0, ∀ x ∈ 𝒜ⁿ, where ≥ is the partial order on the set of all positive elements of 𝒜.” The entrywise star-transpose condition encodes self-adjointness. The double sum is exactly the left-linear Hilbert-module form ⟨Mv,v⟩ = ∑ⱼ∑ₖ Mⱼₖ vₖ star(vⱼ). A centered dot denotes scalar multiplication and juxtaposition denotes algebra multiplication.

**Definition 1.4 (Conjecture 4.3).**

$$\operatorname{claim} \Leftrightarrow (\forall A \in \operatorname{Type},\; [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (2 \le n) \Rightarrow ((2 \le d) \Rightarrow (\forall x \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(d\right) \to A\right),\; (\forall j \in \operatorname{Fin}\left(n\right),\; \forall l \in \operatorname{Fin}\left(d\right),\; \operatorname{IsSelfAdjoint}\left(x\left(j, l\right)\right)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(n\right),\; \forall k \in \operatorname{Fin}\left(n\right),\; \operatorname{star}\left(\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left((\operatorname{fun} (l: \operatorname{Fin}\left(d\right)) \mapsto (2: \mathbb{C})^{-1} \cdot (1 + (2: \mathbb{C})^{-1} \cdot (\operatorname{NormedSpace}.\operatorname{exp}\left(\operatorname{Complex}.\operatorname{I} \cdot (x\left(j, l\right) - x\left(k, l\right))\right) + \operatorname{NormedSpace}.\operatorname{exp}\left(-(\operatorname{Complex}.\operatorname{I} \cdot (x\left(j, l\right) - x\left(k, l\right)))\right))))\right)\right) - (n: \mathbb{C})^{-1} \cdot ((1: A))\right) = \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left((\operatorname{fun} (l: \operatorname{Fin}\left(d\right)) \mapsto (2: \mathbb{C})^{-1} \cdot (1 + (2: \mathbb{C})^{-1} \cdot (\operatorname{NormedSpace}.\operatorname{exp}\left(\operatorname{Complex}.\operatorname{I} \cdot (x\left(k, l\right) - x\left(j, l\right))\right) + \operatorname{NormedSpace}.\operatorname{exp}\left(-(\operatorname{Complex}.\operatorname{I} \cdot (x\left(k, l\right) - x\left(j, l\right)))\right))))\right)\right) - (n: \mathbb{C})^{-1} \cdot ((1: A))) \land (\forall v \in \operatorname{Fin}\left(n\right) \to A,\; 0 \le \sum_{j: \operatorname{Fin}\left(n\right)} \sum_{k: \operatorname{Fin}\left(n\right)} (\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left((\operatorname{fun} (l: \operatorname{Fin}\left(d\right)) \mapsto (2: \mathbb{C})^{-1} \cdot (1 + (2: \mathbb{C})^{-1} \cdot (\operatorname{NormedSpace}.\operatorname{exp}\left(\operatorname{Complex}.\operatorname{I} \cdot (x\left(j, l\right) - x\left(k, l\right))\right) + \operatorname{NormedSpace}.\operatorname{exp}\left(-(\operatorname{Complex}.\operatorname{I} \cdot (x\left(j, l\right) - x\left(k, l\right)))\right))))\right)\right) - (n: \mathbb{C})^{-1} \cdot ((1: A))) v\left(k\right) \operatorname{star}\left(v\left(j\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarNovak.claim` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2021). *C*-algebraic Schur product theorem, Pólya-Szegő-Rudin question and Novak's conjecture*. DOI: [10.48550/arXiv.2108.06662](https://doi.org/10.48550/arXiv.2108.06662). URL: <https://arxiv.org/abs/2108.06662v1>.

*Commentary.*

Conjecture 4.3 (C*-algebraic Novak's conjecture, p. 10): “Let 𝒜 be a unital C*-algebra. Then the matrix [∏_{l=1}^{d} (1+cos (x_{j,l}-x_{k,l}))/2-1/n]_{1≤j,k≤n} is positive for all n,d≥2 and all choices of x_j=(x_{j,1}, …, x_{j,d})∈𝒜_saᵈ, ∀1≤j≤n.” The encoding quantifies A : Type with CStarAlgebra, PartialOrder and StarOrderedRing. Mathlib's CStarAlgebra is unital. The restriction to Type weakens the source's universe range, so negating this restricted claim refutes the source statement. The displayed brackets are anonymous Lean instance arguments.

**Theorem 1.5 (Refutation in two by two complex matrices).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarNovak.result` (`✓ std3`). ∎

*Resolves.* `Problems/krishna-2021-cstar-novak-conjecture` (refuted) by `D5/S3/Quantum/Algebra/CStarNovak.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishna-2021-cstar-novak-conjecture","declaration_gid":"D5/S3/Quantum/Algebra/CStarNovak.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2021). *C*-algebraic Schur product theorem, Pólya-Szegő-Rudin question and Novak's conjecture*. DOI: [10.48550/arXiv.2108.06662](https://doi.org/10.48550/arXiv.2108.06662). URL: <https://arxiv.org/abs/2108.06662v1>.

*Commentary.*

Take n = 3, d = 2 and x j l = A j, with A₁ = 3πI, A₂ = π diag(5,1), and A₃ = (π/4)[[19,√15],[√15,5]]. These are self-adjoint. The three off-diagonal squared differences are 4π²I, 4π²I and π²I. Pairing the exponential-series terms into even and odd powers shows that a scalar square X² = c²I gives ncos X = cos(c)I. Thus the three cosines are I, I and -I, every factor is I or zero, and the matrix is (1/3)[[2,2,2],[2,2,-1],[2,-1,2]] with every entry multiplied by I. At v = (-2,1,1)I its quadratic form is -2I, which is not nonnegative in the matrix positive-semidefinite order. Theorem 4.4 of the source proves the commutative case; this refutation leaves that theorem unaffected.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CStarNovak.IsPositiveMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarNovak.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarNovak.ncos`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarNovak.novakEntry`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarNovak.result`
