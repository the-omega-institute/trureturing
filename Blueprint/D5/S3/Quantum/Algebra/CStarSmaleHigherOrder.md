# A degree-three counterexample to the higher-order C*-algebraic Smale conjecture

## Abstract

The higher-order C*-algebraic Smale mean value conjecture fails at degree three in Complex x Complex with its supremum norm.

**Definition 1.1 (The factor polynomial).**

$$\forall A \in Type,\; [\operatorname{CommRing}\left(A\right)], \forall n \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(n\right) \to A,\; \operatorname{smalePoly}\left(a\right) = \prod_{j: \operatorname{Fin}\left(n\right)}(\operatorname{Polynomial}.\operatorname{X} - \operatorname{Polynomial}.\operatorname{C}\left(a\left(j\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.smalePoly` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*. DOI: [10.48550/arXiv.2206.08154](https://doi.org/10.48550/arXiv.2206.08154). URL: <https://arxiv.org/abs/2206.08154v1>.

*Commentary.*

Section 2, Conjecture HIGHERMEAN (journal p. 44, Conjecture 2.3): "Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜." The polynomial is a product in Polynomial A; its value at z is Polynomial.eval z (smalePoly a). The index j : Fin n denotes the source's a_(j+1), retaining all n factors with multiplicity. The definition applies to every commutative ring; the conjecture specializes it to a commutative C*-algebra.

**Definition 1.2 (Conjecture HIGHERMEAN).**

$$claim \Leftrightarrow (\forall A \in Type,\; [\operatorname{CommCStarAlgebra}\left(A\right)], \forall n \in \mathbb{N},\; 2 \le n \Rightarrow (\forall a \in \operatorname{Fin}\left(n\right) \to A,\; \forall z \in A,\; \operatorname{Polynomial}.\operatorname{eval}\left(z, \operatorname{Polynomial}.\operatorname{derivative}\left(\operatorname{smalePoly}\left(a\right)\right)\right) \ne 0 \Rightarrow (\exists w \in A,\; \operatorname{Polynomial}.\operatorname{eval}\left(w, \operatorname{Polynomial}.\operatorname{derivative}\left(\operatorname{smalePoly}\left(a\right)\right)\right) = 0 \land (\forall k \in \mathbb{N},\; 2 \le k \Rightarrow (k \le n \Rightarrow (\frac{\Vert\operatorname{Polynomial}.\operatorname{eval}\left(z, \operatorname{Function}.\operatorname{iterate}\left(\operatorname{Polynomial}.\operatorname{derivative}, k, \operatorname{smalePoly}\left(a\right)\right)\right)\Vert}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right): \mathbb{R})} \cdot \frac{\Vert\operatorname{Polynomial}.\operatorname{eval}\left(z, \operatorname{smalePoly}\left(a\right)\right) - \operatorname{Polynomial}.\operatorname{eval}\left(w, \operatorname{smalePoly}\left(a\right)\right)\Vert^{k - 1}}{\Vert\operatorname{Polynomial}.\operatorname{eval}\left(z, \operatorname{Polynomial}.\operatorname{derivative}\left(\operatorname{smalePoly}\left(a\right)\right)\right)\Vert^{k}} \le 4^{k - 1}))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.claim` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*. DOI: [10.48550/arXiv.2206.08154](https://doi.org/10.48550/arXiv.2206.08154). URL: <https://arxiv.org/abs/2206.08154v1>.

*Commentary.*

Section 2, Conjecture HIGHERMEAN (journal p. 44, Conjecture 2.3), verbatim: "Let 𝒜 be a commutative C*-algebra. Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜. If z ∈ 𝒜 is not a critical point of P, then there exists a critical point w ∈ 𝒜 of P such that ‖P⁽ᵏ⁾(z)‖/k! · ‖P(z)−P(w)‖ᵏ⁻¹/‖P′(z)‖ᵏ ≤ 4ᵏ⁻¹, ∀ 2 ≤ k ≤ n." CommCStarAlgebra encodes a unital complex commutative C*-algebra. The sum of products with one factor omitted is Polynomial.derivative_prod, and P^(k) is Function.iterate Polynomial.derivative k applied to smalePoly a. Noncritical means the first derivative is nonzero. One w must satisfy every k inequality. Natural subtraction k−1 is truncated subtraction, agreeing with ordinary subtraction for k≥2; factorial is coerced from Nat to Real and every norm and quotient is real-valued. The displayed fractions are division in Real.

**Theorem 1.3 (The higher-order conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture*. DOI: [10.48550/arXiv.2206.08154](https://doi.org/10.48550/arXiv.2206.08154). URL: <https://arxiv.org/abs/2206.08154v1>.

*Commentary.*

Take A = Complex x Complex, n = 3 and z = 0. The roots are (0,0), ((−21+sqrt(437))/2,sqrt(3)) and ((−21−sqrt(437))/2,−sqrt(3)), with real entries embedded into Complex. Their factor product evaluates to (x^3+21x^2+x,y^3−3y). The complete critical set consists of (−7+sqrt(438)/3,1), (−7+sqrt(438)/3,−1), (−7−sqrt(438)/3,1) and (−7−sqrt(438)/3,−1). Its second coordinate forces the norm of P(0)−P(w) to be at least 2. The first and second derivative norms at zero are 3 and 42. Thus the k = 2 expression is at least (42/2)(2/9) = 14/3 > 4 for every critical point. The supremum norm takes the curvature from the first coordinate and the unavoidable critical-value gap from the second; applying the scalar theorem separately does not bound this product of maxima. The source's degree-2 theorem and its scalar higher-order theorem retain their stated scopes.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.result`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.smalePoly`
