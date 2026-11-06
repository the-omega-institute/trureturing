# Ad-invariant principal-log distance: a two-dimensional refutation

## Abstract

A winding shift shortens a trace-coupled quadratic norm while preserving a unitary endpoint.

**Definition 1.1 (Ad-invariant Finsler norm).**

$$\forall n \in \mathbb{N},\; \forall F \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to \mathbb{R},\; \operatorname{IsAdInvariantFinsler}\left(F\right) \Leftrightarrow \left(\left(\left(\left(\left(\left(F(0) = 0 \land \left(\forall z \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; z \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow 0 \le F(z)\right)\right) \land \left(\forall z \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; z \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow \left(F(z) = 0 \Leftrightarrow z = 0\right)\right)\right) \land \left(\forall x \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \forall y \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; x \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow \left(y \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow F(x + y) \le F(x) + F(y)\right)\right)\right) \land \left(\forall r \in \mathbb{R},\; \forall z \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; 0 \le r \Rightarrow \left(z \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow F(r \cdot z) = r \cdot F(z)\right)\right)\right) \land \left(\forall u \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \forall z \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; u \in \operatorname{Matrix.unitaryGroup}(\operatorname{Fin}\left(n\right), \mathbb{C}) \Rightarrow \left(z \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow F(u \cdot z \cdot \operatorname{star}\left(u\right)) = F(z)\right)\right)\right) \land \left(\forall z \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; z \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow \Vert \operatorname{Matrix.toEuclideanCLM}(z)\Vert  \le F(z)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.IsAdInvariantFinsler` (`✓ std3`).

*Citation.* Gabriel Larotonda (2026). *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*. DOI: [10.48550/arXiv.2610.31535](https://doi.org/10.48550/arXiv.2610.31535). URL: <https://arxiv.org/abs/2610.31535v1>.

*Commentary.*

Section 4, p. 5: “Let ‖·‖ be an Ad-invariant Finsler norm on su(n), that is, a subadditive, nondegenerate and positively homogeneous function (‖λv‖=λ‖v‖ for λ≥0) with ‖Adᵤv‖=‖v‖ for u∈SU(n); we do not assume ‖−v‖=‖v‖.” Section 4.1, p. 7 applies this definition to u(n). Matrices outside skewAdjoint impose no restriction. Spectral domination is the normalization of p. 7.

**Definition 1.2 (Piecewise smooth curves).**

$$\forall n \in \mathbb{N},\; \forall gamma \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{PiecewiseSmooth}\left(gamma\right) \Leftrightarrow \left(\operatorname{ContinuousOn}\left(gamma, \operatorname{Set.Icc}(0, 1)\right) \land \left(\exists m \in \mathbb{N},\; \exists tau \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \left(\left(tau(0) = 0 \land tau(\operatorname{Fin.last}(m)) = 1\right) \land \operatorname{StrictMono}\left(tau\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{ContDiffOn}\left(\mathbb{R}, \infty, gamma, \operatorname{Set.Icc}(tau(\operatorname{Fin.castSucc}(j)), tau(\operatorname{Fin.succ}(j)))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.PiecewiseSmooth` (`✓ std3`).

*Citation.* Gabriel Larotonda (2026). *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*. DOI: [10.48550/arXiv.2610.31535](https://doi.org/10.48550/arXiv.2610.31535). URL: <https://arxiv.org/abs/2610.31535v1>.

*Commentary.*

A continuous curve on Set.Icc 0 1 has a finite strictly increasing partition, and is smooth on every closed subinterval. The partition has m pieces and m+1 endpoints.

**Definition 1.3 (Unitary curves with fixed endpoints).**

$$\forall n \in \mathbb{N},\; \forall u \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \forall v \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \forall gamma \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{IsCurve}\left(u, v, gamma\right) \Leftrightarrow \left(\left(\left(\operatorname{PiecewiseSmooth}\left(gamma\right) \land gamma(0) = u\right) \land gamma(1) = v\right) \land \left(\forall t \in \mathbb{R},\; t \in \operatorname{Set.Icc}(0, 1) \Rightarrow gamma(t) \in \operatorname{Matrix.unitaryGroup}(\operatorname{Fin}\left(n\right), \mathbb{C})\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.IsCurve` (`✓ std3`).

*Citation.* Gabriel Larotonda (2026). *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*. DOI: [10.48550/arXiv.2610.31535](https://doi.org/10.48550/arXiv.2610.31535). URL: <https://arxiv.org/abs/2610.31535v1>.

*Commentary.*

The curve starts at u, ends at v, and lies in Matrix.unitaryGroup throughout Set.Icc 0 1.

**Definition 1.4 (Left logarithmic length).**

$$\forall n \in \mathbb{N},\; \forall F \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to \mathbb{R},\; \forall gamma \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{curveLength}\left(F, gamma\right) = \int_{t :\mathbb{R} \in \operatorname{Set.Icc}(0, 1)}^{-} \operatorname{ENNReal.ofReal}(F(\operatorname{star}\left(gamma(t)\right) \cdot \operatorname{deriv}\left(gamma, t\right)))$$

*Formalization.* `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.curveLength` (`✓ std3`).

*Citation.* Gabriel Larotonda (2026). *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*. DOI: [10.48550/arXiv.2610.31535](https://doi.org/10.48550/arXiv.2610.31535). URL: <https://arxiv.org/abs/2610.31535v1>.

*Commentary.*

Section 2.1, p. 2: “The length of a piecewise smooth curve γ⊂U(n) is L(γ)=∫‖γ⁻¹γ̇‖, and d is the induced rectifiable distance, which is bi-invariant.” On unitary matrices star equals inverse. The integral is the extended nonnegative integral for Lebesgue measure on Set.Icc 0 1; finitely many partition points do not affect it.

**Definition 1.5 (Directed rectifiable distance).**

$$\forall n \in \mathbb{N},\; \forall F \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to \mathbb{R},\; \forall u \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \forall v \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{rectifiableDistance}\left(F, u, v\right) = \operatorname{sInf}\left(\{L : \mathbb{R}_{\geq0}^{\infty} \mid \exists gamma \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{IsCurve}\left(u, v, gamma\right) \land L = \operatorname{curveLength}\left(F, gamma\right)\}\right)$$

*Formalization.* `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.rectifiableDistance` (`✓ std3`).

*Citation.* Gabriel Larotonda (2026). *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*. DOI: [10.48550/arXiv.2610.31535](https://doi.org/10.48550/arXiv.2610.31535). URL: <https://arxiv.org/abs/2610.31535v1>.

*Commentary.*

Section 4, p. 5: “Throughout, d(u,w) is the distance from u to w: the infimum of L(γ)=∫‖γ⁻¹γ̇‖ over curves γ starting at u and ending at w.” Empty sets of lengths have infimum infinity.

**Definition 1.6 (The conjectured principal-log formula).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall F \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to \mathbb{R},\; \operatorname{IsAdInvariantFinsler}\left(F\right) \Rightarrow \left(\forall z \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; z \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow \left(\Vert \operatorname{Matrix.toEuclideanCLM}(z)\Vert  \le \operatorname{Real.pi} \Rightarrow \operatorname{rectifiableDistance}\left(F, 1, \operatorname{NormedSpace.exp}(z)\right) = \operatorname{ENNReal.ofReal}(F(z))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.claim` (`✓ std3`).

*Citation.* Gabriel Larotonda (2026). *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*. DOI: [10.48550/arXiv.2610.31535](https://doi.org/10.48550/arXiv.2610.31535). URL: <https://arxiv.org/abs/2610.31535v1>.

*Commentary.*

After Proposition 4.3, p. 7: “It would be natural to conjecture that d(1,eᶻ)=‖z‖ whenever ‖z‖∞≤π.” Here n ranges over positive natural numbers, F over all normalized Ad-invariant Finsler norms, and z over skewAdjoint matrices. No symmetry, trace-zero condition, or singular-value invariance is imposed.

**Theorem 1.7 (The universal equality is false).**

$$\neg (\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall F \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to \mathbb{R},\; \operatorname{IsAdInvariantFinsler}\left(F\right) \Rightarrow \left(\forall z \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; z \in \operatorname{skewAdjoint}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right) \Rightarrow \left(\Vert \operatorname{Matrix.toEuclideanCLM}(z)\Vert  \le \operatorname{Real.pi} \Rightarrow \operatorname{rectifiableDistance}\left(F, 1, \operatorname{NormedSpace.exp}(z)\right) = \operatorname{ENNReal.ofReal}(F(z))\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Larotonda (2026). *Short curves in homogeneous spaces of the unitary group for unitarily invariant norms*. DOI: [10.48550/arXiv.2610.31535](https://doi.org/10.48550/arXiv.2610.31535). URL: <https://arxiv.org/abs/2610.31535v1>.

*Commentary.*

For F(z)²=Σᵢⱼ‖zᵢⱼ‖²+4‖Matrix.trace z‖², use diagonal angles (4π/5,π/2) and (−6π/5,π/2). Their exponentials agree. The smooth exponential curve for the second vector has constant left logarithmic derivative and strictly smaller length, so the infimum is strictly below F at the first vector.

## References

- Truth anchor: `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.IsAdInvariantFinsler`
- Truth anchor: `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.IsCurve`
- Truth anchor: `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.PiecewiseSmooth`
- Truth anchor: `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.curveLength`
- Truth anchor: `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.rectifiableDistance`
- Truth anchor: `D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](../Quantum/Matrix/CommutatorGap.md)
