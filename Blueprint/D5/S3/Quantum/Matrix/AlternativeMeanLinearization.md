# Characterizing rigid alternative means

## Abstract

A scalar characterization of alternative means whose linearizability detects commutation and at most two spectral values.

Dumitru, Franco, and Merino, On The Linearization of Alternative Means, arXiv:2606.25150v1, §1, with the Question restated in Remark 4.4, supplied verbatim: “Question : Can we characterize all functions f : (0, ∞) → (0, ∞) such that Aσ̂_f B is linearizable if and only if AB = BA and |Spec(A⁻¹♯B)| ≤ 2 ?” Definition 2.3 specifies the alternative mean f(A⁻¹♯B) A f(A⁻¹♯B), and Remark 2.2 specifies real coefficients in aA+bB.

**Definition 1.1 (The inverse geometric mean).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{gmInv}\left(A, B\right) = A^{-\frac{1}{2}} \cdot \left(A^{\frac{1}{2}} \cdot B \cdot A^{\frac{1}{2}}\right)^{\frac{1}{2}} \cdot A^{-\frac{1}{2}}$$

*Formalization.* `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.gmInv` (`✓ std3`).

*Citation.* R. Dumitru; J. Franco; A. Merino (2026). *On The Linearization of Alternative Means*. DOI: [10.48550/arXiv.2606.25150](https://doi.org/10.48550/arXiv.2606.25150). URL: <https://arxiv.org/abs/2606.25150v1>.

*Commentary.*

For complex n×n matrices, gmInv A B is A⁻¹ᐟ²(A¹ᐟ²BA¹ᐟ²)¹ᐟ²A⁻¹ᐟ². Each real matrix power displayed here is the continuous functional calculus of x↦xᵖ. For positive definite A and B this is A⁻¹♯B, is positive definite, and is the unique positive definite solution Y of YAY=B, as in equation (1). The definition also exists for other complex matrices through Mathlib's total continuous functional calculus; the geometric interpretation here is restricted to positive definite matrices.

**Definition 1.2 (The alternative mean).**

$$\forall f: \mathbb{R} \to \mathbb{R}, \forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{altMean}\left(f, A, B\right) = \operatorname{cfc}\left(f, \operatorname{gmInv}\left(A, B\right)\right) \cdot A \cdot \operatorname{cfc}\left(f, \operatorname{gmInv}\left(A, B\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.altMean` (`✓ std3`).

*Citation.* R. Dumitru; J. Franco; A. Merino (2026). *On The Linearization of Alternative Means*. DOI: [10.48550/arXiv.2606.25150](https://doi.org/10.48550/arXiv.2606.25150). URL: <https://arxiv.org/abs/2606.25150v1>.

*Commentary.*

Definition 2.3 gives Aσ̂_fB=f(Y)Af(Y), where Y=A⁻¹♯B. The definition uses the real continuous functional calculus on complex Hermitian matrices. The theorem assumes f continuous and positive on (0,∞), with f(1)=1.

**Definition 1.3 (Linearizability).**

$$\forall f: \mathbb{R} \to \mathbb{R}, \forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{Linearizable}\left(f, A, B\right)) \Leftrightarrow (\exists a: \mathbb{R}, \exists b: \mathbb{R}, \operatorname{altMean}\left(f, A, B\right) = (a) \cdot (A) + (b) \cdot (B))$$

*Formalization.* `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.Linearizable` (`✓ std3`).

*Citation.* R. Dumitru; J. Franco; A. Merino (2026). *On The Linearization of Alternative Means*. DOI: [10.48550/arXiv.2606.25150](https://doi.org/10.48550/arXiv.2606.25150). URL: <https://arxiv.org/abs/2606.25150v1>.

*Commentary.*

Remark 2.2 calls the alternative mean linearizable when it equals aA+bB for some real a and b. The coefficients may depend on A and B and need not be positive.

**Definition 1.4 (The property in the Question).**

$$\forall f: \mathbb{R} \to \mathbb{R}, (\operatorname{Rigid}\left(f\right)) \Leftrightarrow (\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{PosDef}\left(A\right)) \Rightarrow ((\operatorname{PosDef}\left(B\right)) \Rightarrow ((\operatorname{Linearizable}\left(f, A, B\right)) \Leftrightarrow ((A \cdot B = B \cdot A) \land (\operatorname{ncard}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{gmInv}\left(A, B\right)\right)\right) \le 2)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.Rigid` (`✓ std3`).

*Citation.* R. Dumitru; J. Franco; A. Merino (2026). *On The Linearization of Alternative Means*. DOI: [10.48550/arXiv.2606.25150](https://doi.org/10.48550/arXiv.2606.25150). URL: <https://arxiv.org/abs/2606.25150v1>.

*Commentary.*

Rigid f requires, for every finite dimension n and every pair of complex positive definite matrices A and B, that the alternative mean be linearizable exactly when A and B commute and the real spectrum of A⁻¹♯B has at most two values. The quantifier includes dimension zero; its spectrum is empty and its matrices are unique.

**Lemma 1.5 (The positive half-power is the square root).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{PosDef}\left(A\right)) \Rightarrow (\operatorname{cfc}\left((\lambda x: \mathbb{R}, x^{\frac{1}{2}}), A\right) = \operatorname{sqrt}\left(A\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.half_eq_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Dumitru; J. Franco; A. Merino (2026). *On The Linearization of Alternative Means*. DOI: [10.48550/arXiv.2606.25150](https://doi.org/10.48550/arXiv.2606.25150). URL: <https://arxiv.org/abs/2606.25150v1>.

*Commentary.*

For every positive definite complex matrix, the real functional calculus of x to the power one half equals its positive square root.

**Lemma 1.6 (The two half-powers are mutual inverses).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{PosDef}\left(A\right)) \Rightarrow ((\operatorname{cfc}\left((\lambda x: \mathbb{R}, x^{\frac{1}{2}}), A\right) \cdot \operatorname{cfc}\left((\lambda x: \mathbb{R}, x^{-\frac{1}{2}}), A\right) = 1) \land (\operatorname{cfc}\left((\lambda x: \mathbb{R}, x^{-\frac{1}{2}}), A\right) \cdot \operatorname{cfc}\left((\lambda x: \mathbb{R}, x^{\frac{1}{2}}), A\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.half_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Dumitru; J. Franco; A. Merino (2026). *On The Linearization of Alternative Means*. DOI: [10.48550/arXiv.2606.25150](https://doi.org/10.48550/arXiv.2606.25150). URL: <https://arxiv.org/abs/2606.25150v1>.

*Commentary.*

For every positive definite complex matrix, its real functional calculus powers one half and minus one half multiply to the identity in both orders.

**Theorem 1.7 (Necessary and sufficient scalar conditions).**

$$\forall f: \mathbb{R} \to \mathbb{R}, ((\operatorname{ContinuousOn}\left(f, \operatorname{Ioi}\left(0\right)\right)) \land ((\forall x: \mathbb{R}, (0 < x) \Rightarrow (0 < \operatorname{f}\left(x\right))) \land (\operatorname{f}\left(1\right) = 1))) \Rightarrow ((\operatorname{Rigid}\left(f\right)) \Leftrightarrow ((\operatorname{InjOn}\left(f, \operatorname{Ioi}\left(0\right)\right)) \land ((\operatorname{InjOn}\left((\lambda x, \frac{\operatorname{f}\left(x\right)}{x}), \operatorname{Ioi}\left(0\right)\right)) \land ((\operatorname{StrictConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), (\lambda s, \operatorname{f}\left(\operatorname{sqrt}\left(s\right)\right)^{2})\right)) \lor (\operatorname{StrictConcaveOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), (\lambda s, \operatorname{f}\left(\operatorname{sqrt}\left(s\right)\right)^{2})\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.result` (`✓ std3`). ∎

*Resolves.* `Problems/dumitru-franco-merino-2026-alternative-mean-linearization` (proved) by `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dumitru-franco-merino-2026-alternative-mean-linearization","declaration_gid":"D5/S3/Quantum/Matrix/AlternativeMeanLinearization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Dumitru; J. Franco; A. Merino (2026). *On The Linearization of Alternative Means*. DOI: [10.48550/arXiv.2606.25150](https://doi.org/10.48550/arXiv.2606.25150). URL: <https://arxiv.org/abs/2606.25150v1>.

*Commentary.*

Let g(s)=f(√s)². Rigidity is equivalent to injectivity of f and x↦f(x)/x on (0,∞), together with strict convexity or strict concavity of g there. To prove sufficiency, diagonalize Y=U diag(t) U* and put C=U*AU. Linearizability gives (f(tᵢ)f(tⱼ)−a−btᵢtⱼ)Cᵢⱼ=0. Positivity of Cᵢᵢ gives f(tᵢ)²=a+btᵢ², so strict convexity or concavity excludes three distinct spectral values. For distinct x,y, writing u=f(x), v=f(y), the coefficient is uv−a−bxy=−(u−v)(yu−xv)/(x+y). The two injectivity conditions make it nonzero. Thus C has zero entries between distinct eigenspaces, A commutes with Y, and A commutes with B=YAY. Conversely, commutation of A and B propagates through the functional calculus defining Y. On at most two spectral values, interpolation gives f(t)²=a+bt² and hence f(Y)Af(Y)=aA+bB. For necessity, take A=[[2,1],[1,2]], Y=diag(x,y), and B=YAY. Equal values f(x)=f(y)=c give the mean c²A; equal quotients f(x)/x=f(y)/y=c give c²B. Both are linearizable, while (AB−BA)₁₂=2(y²−x²) is nonzero for distinct positive x,y. Finally, a collinear triple (s,g(s)),(t,g(t)),(u,g(u)) with 0<s<t<u yields the linearizable pair A=I, B=diag(s,t,u), with three distinct values in the spectrum of Y=diag(√s,√t,√u). The adjacent-slope difference is therefore nonzero. Continuity on the convex domain 0<s<t<u makes its sign constant, giving strict convexity or strict concavity of g. The theorem concerns D=ℂ. The same spectral argument over real or quaternionic matrices is mathematical reasoning and is not formalized here. The supplied quotation is tied to arXiv:2606.25150v1; agreement with the author text is ASSUMED-UNVERIFIED. No exhaustive literature or priority claim is established.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.Linearizable`
- Truth anchor: `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.Rigid`
- Truth anchor: `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.altMean`
- Truth anchor: `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.gmInv`
- Truth anchor: `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.half_eq_sqrt`
- Truth anchor: `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.half_inverse`
- Truth anchor: `D5/S3/Quantum/Matrix/AlternativeMeanLinearization.result`
