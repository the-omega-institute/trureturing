# The degree polynomial root bound

## Abstract

Every nonzero degree root satisfies the Brown–George argument-dependent modulus bound.

**Definition 1.1 (The degree polynomial).**

$$\forall n \in \operatorname{Nat},\; \forall G \in SimpleGraph\left(Fin\left(n\right)\right),\; degreePolynomial\left(G\right) = \sum_{(v:Fin\left(n\right))}\operatorname{Polynomial}.\operatorname{X}^{G.degree\left(v\right)}$$

*Formalization.* `D5/S3/Zeros/DegreeRoots/Result.degreePolynomial` (`✓ std3`).

*Citation.* J. I. Brown and I. C. George (2025). *On the roots of degree polynomials*. DOI: [10.48550/arXiv.2505.04882](https://doi.org/10.48550/arXiv.2505.04882). URL: <https://arxiv.org/abs/2505.04882v1>.

*Commentary.*

Section 1, p. 164: “For any v ∈ V, let deg(v) = deg_G(v) denote its degree in G, and let a_k be the number of vertices of degree k in G. The degree polynomial of G is defined by” D(G;x)=Σ_{v∈V} x^{deg(v)}=Σ_{k=δ}^{Δ} a_k x^k. Here G is a simple graph on Fin n, and Polynomial.X has complex coefficients. The sum counts every vertex once, including vertices of degree zero.

**Definition 1.2 (Conjecture 4.1).**

$$claim = (\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\forall G \in SimpleGraph\left(Fin\left(n\right)\right),\; \forall z \in \operatorname{Complex},\; z \ne 0 \Rightarrow \left((degreePolynomial\left(G\right)).eval\left(z\right) = 0 \Rightarrow \left\lVert z \right\rVert \le ((n:\operatorname{Real})-1)^{\frac{\left|\operatorname{Complex}.\operatorname{arg}\left(z\right)\right|}{\operatorname{Real}.\operatorname{pi}}}\right)\right))$$

*Formalization.* `D5/S3/Zeros/DegreeRoots/Result.claim` (`✓ std3`).

*Citation.* J. I. Brown and I. C. George (2025). *On the roots of degree polynomials*. DOI: [10.48550/arXiv.2505.04882](https://doi.org/10.48550/arXiv.2505.04882). URL: <https://arxiv.org/abs/2505.04882v1>.

*Commentary.*

Conjecture 4.1, p. 180: “If z is a nonzero degree root of a graph of order n with argument arg(z) ∈ (−π, π], then |z| ≤ (n − 1)^{|arg(z)/π|}.” The order is a positive natural number n; the vertices are Fin n. Complex.arg takes values in (−π, π], the modulus is the complex norm, and the real power has exponent |Complex.arg z|/Real.pi. Since Real.pi is positive, this exponent equals |arg(z)/π|.

**Theorem 1.3 (Conjecture 4.1 holds).**

$$\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\forall G \in SimpleGraph\left(Fin\left(n\right)\right),\; \forall z \in \operatorname{Complex},\; z \ne 0 \Rightarrow \left((degreePolynomial\left(G\right)).eval\left(z\right) = 0 \Rightarrow \left\lVert z \right\rVert \le ((n:\operatorname{Real})-1)^{\frac{\left|\operatorname{Complex}.\operatorname{arg}\left(z\right)\right|}{\operatorname{Real}.\operatorname{pi}}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/DegreeRoots/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/brown-george-2025-degree-polynomial-root-bound` (proved) by `D5/S3/Zeros/DegreeRoots/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"brown-george-2025-degree-polynomial-root-bound","declaration_gid":"D5/S3/Zeros/DegreeRoots/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. I. Brown and I. C. George (2025). *On the roots of degree polynomials*. DOI: [10.48550/arXiv.2505.04882](https://doi.org/10.48550/arXiv.2505.04882). URL: <https://arxiv.org/abs/2505.04882v1>.

*Commentary.*

For roots outside the unit disk, divide the polynomial equation by its largest degree power. The vertices of maximum degree contribute a positive constant. The normalized inverse-power estimate bounds the norm by the ratio of the remaining vertex count to that constant, raised to |Complex.arg z|/Real.pi. This ratio is at most n−1. For n at least two, roots in the unit disk satisfy the same bound; for n=1 the degree polynomial is one and has no roots.

## References

- Truth anchor: `D5/S3/Zeros/DegreeRoots/Result.claim`
- Truth anchor: `D5/S3/Zeros/DegreeRoots/Result.degreePolynomial`
- Truth anchor: `D5/S3/Zeros/DegreeRoots/Result.result`
- Dependency: [D5/S3/Zeros/DegreeRoots/EscapeWitness](EscapeWitness.md)
