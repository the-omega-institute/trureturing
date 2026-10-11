# CStarSendovCommutative

## Abstract

Dense invertibles and the literal C*-derivative give the commutative Sendov refutation.

**Definition 1.1 (The C*-algebraic derivative).**

$$\forall A:Type, [\operatorname{NormedRing}\left(A\right)] \forall f:A \to A, \forall w:A, \forall L:A, (\operatorname{HasCStarDeriv}\left(f, w, L\right)) \Leftrightarrow (\forall e:\mathbb{R}, (0 < e) \Rightarrow (\exists d:\mathbb{R}, (0 < d) \land (\forall z:A, (\left\lVert z - w \right\rVert < d) \Rightarrow ((\operatorname{IsUnit}\left(z - w\right)) \Rightarrow (\left\lVert \operatorname{Ring}.\operatorname{inverse}\left(z - w\right) \cdot \left((f)\left(z\right) - (f)\left(w\right)\right) - L \right\rVert < e)))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendovCommutative.HasCStarDeriv` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Definition 2.1 (C*-algebraic differentiation), p. 2: “Let 𝒜 be a unital commutative C*-algebra and G(𝒜) be dense in 𝒜. Let f: 𝒜→𝒜 be a function and ω∈𝒜. We say that f is C*-algebraic differentiable at ω if there exists an L∈𝒜 satisfying the following: for each ε>0, there exists a δ>0 such that if z∈𝒜 satisfies ‖z−ω‖<δ and z−ω∈G(𝒜), then ‖(z−ω)⁻¹(f(z)−f(ω))−L‖<ε. In this case, we write f′(ω)=L.” The predicate states the displayed condition for a specified L. Dense invertibles are required by the claim. Ring.inverse agrees with the unit inverse on the tested increments.

**Definition 1.2 (Krishna's Conjecture 2.4).**

$$(claimSendovCommutative) \Leftrightarrow (\forall A:Type, [\operatorname{CommCStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] (\operatorname{Dense}\left(\{x:A\mid\operatorname{IsUnit}\left(x\right)\}\right)) \Rightarrow (\forall n:\mathbb{N}, (2 \le n) \Rightarrow (\forall a:\operatorname{Fin}\left(n\right) \to A, (\forall j:\operatorname{Fin}\left(n\right), (a)\left(j\right) \in \operatorname{cstarDisc}\left(0, 1\right)) \Rightarrow (\forall b:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right) \to A, (\forall k:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right), \operatorname{HasCStarDeriv}\left(\operatorname{CStarDualMeanValue}.\operatorname{orderedPoly}\left(a\right), (b)\left(k\right), 0\right)) \Rightarrow ((\forall k:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right), (b)\left(k\right) \in \operatorname{cstarDisc}\left(0, 1\right)) \Rightarrow ((\forall k:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right), \operatorname{IsConvexForm}\left(a, (b)\left(k\right)\right)) \Rightarrow (\forall j:\operatorname{Fin}\left(n\right), \exists z:A, (\operatorname{HasCStarDeriv}\left(\operatorname{CStarDualMeanValue}.\operatorname{orderedPoly}\left(a\right), z, 0\right)) \land (z \in \operatorname{cstarDisc}\left((a)\left(j\right), 1\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendovCommutative.claimSendovCommutative` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Conjecture 2.4, p. 3: “Let 𝒜 be a unital commutative C*-algebra and G(𝒜) be dense in 𝒜. Let n ∈ ℕ∖{1} and p(z)=(z−a₁)(z−a₂)⋯(z−aₙ)∈𝒜[z] be such that a₁, a₂, …, aₙ ∈ 𝔻̅*(0,1). Assume that p′ admits roots in 𝒜, say b₁, b₂, …, bₙ₋₁ ∈ 𝔻̅*(0,1) and each bₖ can be written in the form of Equation (1). Then for each aⱼ, 1≤j≤n, there exists a zero b of p′ such that b ∈ 𝔻̅*(aⱼ,1).” The encoding uses zero-based Fin indices, degrees 2≤n, and unital commutative C*-algebras in Type with PartialOrder and StarOrderedRing. A zero at z is HasCStarDeriv (orderedPoly a) z 0. For every root the conclusion asks for an algebra-valued derivative zero in its unit disc.

**Theorem 1.3 (Conjecture 2.4 is false).**

$$\neg claimSendovCommutative$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendovCommutative.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Invertibles are dense in C(Set.Icc 0 6,ℂ): polynomial approximation gives a smooth approximant, and its image has dense complement by the real dimension inequality. A small translation avoids zero. For the cubic, the exact invertible-increment identity identifies Definition 2.1 with orderedDeriv. The two critical branches then give the same obstruction to the disc around 1/2.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendovCommutative.HasCStarDeriv`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendovCommutative.claimSendovCommutative`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendovCommutative.result`
- Dependency: [D5/S3/Quantum/Algebra/CStarDualMeanValue](CStarDualMeanValue.md)
- Dependency: [D5/S3/Quantum/Algebra/CStarSendov](CStarSendov.md)
