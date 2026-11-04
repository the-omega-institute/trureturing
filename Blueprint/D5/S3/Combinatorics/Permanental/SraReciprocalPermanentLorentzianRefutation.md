# Sra: reciprocal-permanent Lorentzian assertion

## Abstract

The reciprocal-permanent polynomial of a positive inverse M matrix need not be Lorentzian.

**Definition 1.1 (InverseMMatrix).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{InverseMMatrix}\left(A\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; 0 \le A\left(i, j\right)) \land ((\operatorname{IsUnit}\left(\operatorname{Matrix}.\operatorname{det}\left(A\right)\right)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (i \ne j) \Rightarrow (\left(A^{-1}\right)\left(i, j\right) \le 0))))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.InverseMMatrix` (`✓ std3`).

*Citation.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

Source, p. 1: “A matrix A is an inverse M-matrix if A≥0 entrywise, A is invertible, and A^{-1} has nonpositive off-diagonal entries.” Invertibility is expressed by IsUnit of the determinant; indices are Fin n.

**Definition 1.2 (reciprocalPolynomial).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \operatorname{reciprocalPolynomial}\left(A\right) = (\sum_{S:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)} (\operatorname{C}\left(\operatorname{PSW}.\operatorname{principalPermanent}\left(A, S\right)^{-1}\right) \cdot \operatorname{X}\left(none\right)^{\operatorname{Nat}.\operatorname{sub}\left(n, \operatorname{Finset}.\operatorname{card}\left(S\right)\right)} \cdot (\prod_{i\in S} (\operatorname{X}\left(\operatorname{some}\left(i\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.reciprocalPolynomial` (`✓ std3`).

*Citation.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

Source, p. 6, §4(d): “For an inverse M-matrix A, consider” the displayed sum f_A(x_0,x)=∑_{S⊆[n]} per(A_S)⁻¹ x_0^{n−|S|} ∏_{i∈S} x_i. The variable none is x₀ and some i is the paper's variable xᵢ₊₁. PSW.principalPermanent uses Matrix.permanent on the subtype S; the empty permanent and product are one. Nat.sub in the exponent is truncated natural subtraction.

**Definition 1.3 (positiveHomogeneous).**

$$\forall n \in \mathbb {N},\; \forall d \in \mathbb {N},\; \forall f \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; (\operatorname{positiveHomogeneous}\left(d, f\right)) \Leftrightarrow ((\operatorname{MvPolynomial}.\operatorname{IsHomogeneous}\left(f, d\right)) \land (\forall a \in \operatorname{Finsupp}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {N}\right),\; (\operatorname{Finsupp}.\operatorname{sum}\left(a, fun \mathord{\cdot} k \mapsto k\right) = d) \Rightarrow (0 < \operatorname{coeff}\left(f, a\right))))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.positiveHomogeneous` (`✓ std3`).

*Citation.* Petter Brändén, June Huh (2020). *Lorentzian polynomials*. DOI: [10.4007/annals.2020.192.3.4](https://doi.org/10.4007/annals.2020.192.3.4). URL: <https://arxiv.org/abs/1902.03719v8>.

*Commentary.*

Brändén–Huh, p. 6, §2.1: “We write H⁽ᵈ⁾ₙ for the set of degree d homogeneous polynomials in ℝ[w₁,…,wₙ].” “We define a topology on H⁽ᵈ⁾ₙ using the Euclidean norm for the coefficients, and write P⁽ᵈ⁾ₙ ⊆ H⁽ᵈ⁾ₙ for the open subset of polynomials all of whose coefficients are positive.” The formula quantifies over all degree-d exponents, including exponents outside a polynomial's support. The centered dot in the lambda denotes Lean's anonymous unused index binder _.

**Definition 1.4 (quadraticHessian).**

$$\forall n \in \mathbb {N},\; \forall f \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; \operatorname{quadraticHessian}\left(f\right) = fun (i : \operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto fun (j : \operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{coeff}\left(\operatorname{pderiv}\left(i, \operatorname{pderiv}\left(j, f\right)\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.quadraticHessian` (`✓ std3`).

*Citation.* Petter Brändén, June Huh (2020). *Lorentzian polynomials*. DOI: [10.4007/annals.2020.192.3.4](https://doi.org/10.4007/annals.2020.192.3.4). URL: <https://arxiv.org/abs/1902.03719v8>.

*Commentary.*

Brändén–Huh, p. 6, §2.1: “The Hessian of f ∈ ℝ[w₁,…,wₙ] is the symmetric matrix” ℋ_f(w)=(∂ᵢ∂ⱼf)ᵢ,ⱼ, “where ∂ᵢ stands for the partial derivative ∂/∂wᵢ.” For a homogeneous quadratic these derivatives are constant, so their coefficients at exponent zero give that matrix.

**Definition 1.5 (strictlyLorentzian).**

$$\begin{aligned}\forall n \in \mathbb {N},\; \forall f \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; (\operatorname{strictlyLorentzian}\left(0, f\right)) \Leftrightarrow (\operatorname{positiveHomogeneous}\left(0, f\right))\\\forall n \in \mathbb {N},\; \forall f \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; (\operatorname{strictlyLorentzian}\left(1, f\right)) \Leftrightarrow (\operatorname{positiveHomogeneous}\left(1, f\right))\\\forall n \in \mathbb {N},\; \forall f \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; (\operatorname{strictlyLorentzian}\left(2, f\right)) \Leftrightarrow ((\operatorname{positiveHomogeneous}\left(2, f\right)) \land (\exists h \in \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{quadraticHessian}\left(f\right)\right),\; (\forall i \in \operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{IsHermitian}.\operatorname{eigenvalues}\left(h, i\right) \ne 0) \land (\exists! (i : \operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)) , 0 < \operatorname{IsHermitian}.\operatorname{eigenvalues}\left(h, i\right))))\\\forall n \in \mathbb {N},\; \forall k \in \mathbb {N},\; \forall f \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; (\operatorname{strictlyLorentzian}\left(k + 3, f\right)) \Leftrightarrow ((\operatorname{positiveHomogeneous}\left(k + 3, f\right)) \land (\forall i \in \operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{strictlyLorentzian}\left(k + 2, \operatorname{pderiv}\left(i, f\right)\right)))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.strictlyLorentzian` (`✓ std3`).

*Citation.* Petter Brändén, June Huh (2020). *Lorentzian polynomials*. DOI: [10.4007/annals.2020.192.3.4](https://doi.org/10.4007/annals.2020.192.3.4). URL: <https://arxiv.org/abs/1902.03719v8>.

*Commentary.*

Brändén–Huh, p. 7, Definition 2.1: “We set L̊⁰ₙ=P⁰ₙ, L̊¹ₙ=P¹ₙ, and L̊²ₙ={f∈P²ₙ | ℋ_f is nonsingular and has exactly one positive eigenvalue}.” “For d larger than 2, we define L̊ᵈₙ recursively by setting L̊ᵈₙ={f∈Pᵈₙ | ∂ᵢf∈L̊ᵈ⁻¹ₙ for all i∈[n]}.” The variable set here is Option(Fin n). The Hermitian eigenvalue index counts multiplicity; every eigenvalue is nonzero and exactly one index has a positive eigenvalue.

**Definition 1.6 (Lorentzian).**

$$\forall n \in \mathbb {N},\; \forall d \in \mathbb {N},\; \forall f \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; (\operatorname{Lorentzian}\left(d, f\right)) \Leftrightarrow ((\operatorname{MvPolynomial}.\operatorname{IsHomogeneous}\left(f, d\right)) \land (\forall epsilon \in \mathbb {R},\; (0 < epsilon) \Rightarrow (\exists g \in \operatorname{MvPolynomial}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {R}\right),\; (\operatorname{strictlyLorentzian}\left(d, g\right)) \land (\forall a \in \operatorname{Finsupp}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), \mathbb {N}\right),\; (\operatorname{Finsupp}.\operatorname{sum}\left(a, fun \mathord{\cdot} k \mapsto k\right) = d) \Rightarrow (\left|\operatorname{coeff}\left(g, a\right) - \operatorname{coeff}\left(f, a\right)\right| < epsilon)))))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.Lorentzian` (`✓ std3`).

*Citation.* Petter Brändén, June Huh (2020). *Lorentzian polynomials*. DOI: [10.4007/annals.2020.192.3.4](https://doi.org/10.4007/annals.2020.192.3.4). URL: <https://arxiv.org/abs/1902.03719v8>.

*Commentary.*

Brändén–Huh, p. 7, Definition 2.1: “The polynomials in L̊⁽ᵈ⁾ₙ are called strictly Lorentzian, and the limits of strictly Lorentzian polynomials are called Lorentzian.” The coefficient epsilon condition expresses closure in the finite-dimensional homogeneous degree-d space. The centered dot in the lambda denotes Lean's anonymous unused index binder _.

**Definition 1.7 (claim).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb {N},\; (0 < n) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{InverseMMatrix}\left(A\right)) \Rightarrow (\operatorname{Lorentzian}\left(n, \operatorname{reciprocalPolynomial}\left(A\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.claim` (`✓ std3`).

*Citation.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

Source, p. 6, §4(d): “Is f_A Lorentzian for every inverse M-matrix A?” The assertion quantifies over every n>0 and every real n×n inverse M matrix, with no symmetry hypothesis. Fin n index i is source index i+1.

**Theorem 1.8 (result).**

$$\neg (\forall n \in \mathbb {N},\; (0 < n) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{InverseMMatrix}\left(A\right)) \Rightarrow (\operatorname{Lorentzian}\left(n, \operatorname{reciprocalPolynomial}\left(A\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sra2609-koteljanskii` (refuted) by `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sra2609-koteljanskii","declaration_gid":"D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

The 5×5 matrix of Sra's Theorem 1.2 has positive entries and an inverse with nonpositive off-diagonal entries. Differentiating in its last three variables gives a quadratic whose Hessian is positive definite on span(e₀,e₁+e₂). This property persists for sufficiently close coefficient approximations, whereas every strictly Lorentzian quadratic has only one positive eigenvalue.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.InverseMMatrix`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.Lorentzian`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.positiveHomogeneous`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.quadraticHessian`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.reciprocalPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.strictlyLorentzian`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain](PanSkanderaWangAllSplitsChain.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../../Quantum/Matrix/SpectralPower.md)
