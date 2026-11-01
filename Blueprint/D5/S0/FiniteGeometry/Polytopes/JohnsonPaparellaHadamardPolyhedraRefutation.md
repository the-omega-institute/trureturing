# A Hadamard-closed cone that is not a spectracone

## Abstract

Hadamard closure does not imply exact spectracone representation.

**Definition 1.1 (Real half-spaces in complex coordinates).**

$$\forall n: \mathbb{N}, \forall a: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall b: \mathbb{R}, \operatorname{halfSpace}\left(a, b\right)=\{x: \operatorname{Fin}\left(n\right) \to \mathbb{C}\mid b\leq \operatorname{Complex}.\operatorname{re}\left((\sum_{i: \operatorname{Fin}\left(n\right)}\operatorname{star}\left(\operatorname{a}\left(i\right)\right)\cdot \operatorname{x}\left(i\right))\right)\}$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.halfSpace` (`✓ std3`).

*Citation.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

Page 5, Section 2.3: “If a ∈ ℂⁿ, a ≠ 0, and b ∈ ℝ, then” H(a,b) := {x ∈ ℂⁿ | Re(⟨a, x⟩) ≥ b} = {x ∈ ℂⁿ | Re(⟨x, a⟩) ≥ b} “is a closed half-space determined by the hyperplane {x ∈ ℂⁿ | Re(⟨x, a⟩) = b}.” The finite coordinates are Fin n, and the conjugate of a multiplies x in the displayed sum. Nonzero normals are required by the finite-intersection definitions below.

**Definition 1.2 (Finite intersections of half-spaces).**

$$\forall n: \mathbb{N}, \forall K: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right), \operatorname{IsSourcePolyhedron}\left(K\right)\iff \exists m: \mathbb{N}, (0<m)\land (\exists a: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right), \exists b: \operatorname{Fin}\left(m\right) \to \mathbb{R}, (\forall j: \operatorname{Fin}\left(m\right), \operatorname{a}\left(j\right)\neq 0)\land (K=\{x: \operatorname{Fin}\left(n\right) \to \mathbb{C}\mid \forall j: \operatorname{Fin}\left(m\right), x\in \operatorname{halfSpace}\left(\operatorname{a}\left(j\right), \operatorname{b}\left(j\right)\right)\}))$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.IsSourcePolyhedron` (`✓ std3`).

*Citation.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

Page 5, Section 2.3: “Any set of the form” ⋂ₖ₌₁ᵐ H(aₖ,bₖ) = ⋂ₖ₌₁ᵐ {x ∈ ℂⁿ | Re(⟨aₖ, x⟩) ≥ bₖ} “is called a polyhedron and a bounded polyhedron is called a polytope.” The number m is positive, every normal is nonzero, and each member of Fin m supplies one inequality.

**Definition 1.3 (Bounded polyhedra).**

$$\forall n: \mathbb{N}, \forall K: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right), \operatorname{IsSourcePolytope}\left(K\right)\iff (\operatorname{IsSourcePolyhedron}\left(K\right))\land (\operatorname{Bornology}.\operatorname{IsBounded}\left(K\right))$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.IsSourcePolytope` (`✓ std3`).

*Citation.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

Page 5, Section 2.3: “is called a polyhedron and a bounded polyhedron is called a polytope.” Boundedness is Bornology.IsBounded for the usual metric on the finite complex function space.

**Definition 1.4 (Homogeneous half-spaces).**

$$\forall n: \mathbb{N}, \forall K: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right), \operatorname{IsSourcePolyhedralCone}\left(K\right)\iff \exists m: \mathbb{N}, (0<m)\land (\exists a: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right), (\forall j: \operatorname{Fin}\left(m\right), \operatorname{a}\left(j\right)\neq 0)\land (K=\{x: \operatorname{Fin}\left(n\right) \to \mathbb{C}\mid \forall j: \operatorname{Fin}\left(m\right), x\in \operatorname{halfSpace}\left(\operatorname{a}\left(j\right), 0\right)\}))$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.IsSourcePolyhedralCone` (`✓ std3`).

*Citation.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

Page 5, Section 2.3: “Any set of the form” ⋂ₖ₌₁ᵐ H(aₖ) = {x ∈ ℂⁿ | Re(⟨aₖ, x⟩) ≥ 0} “is called a polyhedral cone.” The finite intersection requires every index k; H(a) means H(a,0). All half-spaces are real, including those that impose imaginary-coordinate equalities.

**Definition 1.5 (The spectracone of a matrix).**

$$\forall n: \mathbb{N}, \forall S: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{spectracone}\left(S\right)=\{x: \operatorname{Fin}\left(n\right) \to \mathbb{C}\mid \forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (0: \mathbb{C})\leq (S\cdot \operatorname{Matrix}.\operatorname{diagonal}\left(x\right)\cdot S^{-1})\left(i, j\right)\}$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.spectracone` (`✓ std3`).

*Citation.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

Page 10, Definition 4.1: “If S ∈ GLₙ(ℂ), then:” “𝒞(S) := {x ∈ ℂⁿ | Mₓ := SDₓS⁻¹ ≥ 0} is called the (Perron) spectracone of S;”. Matrix.diagonal x is Dₓ. The complex order requires both a nonnegative real part and zero imaginary part in every entry. The formula defines the set for every square S; invertibility is required in the representation assertion.

**Definition 1.6 (The stochastic cross-section).**

$$\forall n: \mathbb{N}, \forall S: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{spectratope}\left(S\right)=\{x: \operatorname{Fin}\left(n\right) \to \mathbb{C}\mid (x\in \operatorname{spectracone}\left(S\right))\land (\operatorname{Matrix}.\operatorname{mulVec}\left((S\cdot \operatorname{Matrix}.\operatorname{diagonal}\left(x\right)\cdot S^{-1}), (1: \operatorname{Fin}\left(n\right) \to \mathbb{C})\right)=1)\}$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.spectratope` (`✓ std3`).

*Citation.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

Page 10, Definition 4.1: “𝒫(S) := {x ∈ 𝒞(S) | Mₓe = e} is called the (Perron) spectratope of S;”. The function 1 is the all-ones vector e, and Matrix.mulVec expresses the row-sum equation.

**Definition 1.7 (Question 9.1).**

$$\operatorname{claim}\iff (\forall n: \mathbb{N}, 0<n\implies \forall K: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right), (\operatorname{IsSourcePolyhedralCone}\left(K\right)\implies (\forall x: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall y: \operatorname{Fin}\left(n\right) \to \mathbb{C}, x\in K\implies y\in K\implies x\cdot y\in K)\implies \exists S: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{Matrix}.\operatorname{det}\left(S\right)\neq 0)\land (K=\operatorname{spectracone}\left(S\right)))\land (\operatorname{IsSourcePolytope}\left(K\right)\implies (\forall x: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall y: \operatorname{Fin}\left(n\right) \to \mathbb{C}, x\in K\implies y\in K\implies x\cdot y\in K)\implies \exists S: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{Matrix}.\operatorname{det}\left(S\right)\neq 0)\land (K=\operatorname{spectratope}\left(S\right))))$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.claim` (`✓ std3`).

*Citation.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

Page 27, Question 9.1: “If K is a polyhedral cone (polytope) that is closed with respect to the Hadamard product, is there an invertible matrix S such that K = 𝒞(S) (K = 𝒫(S))?” The proposition asks both converses for every positive n and every subset of Fin n → ℂ. Vector multiplication is coordinatewise. The diagonalizer has the same size n; no identity, dimension, pointedness or spectral-admissibility condition is added.

**Theorem 1.8 (A negative answer to Question 9.1).**

$$\neg (\forall n: \mathbb{N}, 0<n\implies \forall K: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right), (\operatorname{IsSourcePolyhedralCone}\left(K\right)\implies (\forall x: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall y: \operatorname{Fin}\left(n\right) \to \mathbb{C}, x\in K\implies y\in K\implies x\cdot y\in K)\implies \exists S: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{Matrix}.\operatorname{det}\left(S\right)\neq 0)\land (K=\operatorname{spectracone}\left(S\right)))\land (\operatorname{IsSourcePolytope}\left(K\right)\implies (\forall x: \operatorname{Fin}\left(n\right) \to \mathbb{C}, \forall y: \operatorname{Fin}\left(n\right) \to \mathbb{C}, x\in K\implies y\in K\implies x\cdot y\in K)\implies \exists S: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{Matrix}.\operatorname{det}\left(S\right)\neq 0)\land (K=\operatorname{spectratope}\left(S\right))))$$

*Proof.* Machine-checked in Lean as `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/jp2025` (refuted) by `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jp2025","declaration_gid":"D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Charles R. Johnson; Pietro Paparella (2025). *Perron similarities and the nonnegative inverse eigenvalue problem*. DOI: [10.1090/tran/9596](https://doi.org/10.1090/tran/9596). URL: <https://arxiv.org/abs/2409.07682v4>.

*Commentary.*

The explicit m = 10 cone in three coordinates has fourteen real supporting inequalities and three reality equations. Products of its generators lie in the cone, and a nonnegative three-generator decomposition extends this property to all cone points. Ten boundary edge midpoints require distinct active nonzero linear forms. A three-by-three complex diagonalizer supplies nine entry forms, and their imaginary parts vanish on the real span. The resulting contradiction refutes the cone converse and hence the conjunction in Question 9.1. The unbounded family and the separate polytope converse are outside this theorem.

## References

- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.IsSourcePolyhedralCone`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.IsSourcePolyhedron`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.IsSourcePolytope`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.claim`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.halfSpace`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.result`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.spectracone`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.spectratope`
