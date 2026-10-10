# Gazeau's Schwartz action admits no normal Hilbert realization

## Abstract

The ordinary Gazeau block action on the full Schwartz core has no closed densely defined self-adjoint, skew-adjoint, or normal realization under any complete positive Hilbert metric on the fixed complex vector space.

**Definition 1.1 (The Lebesgue L2 embedding).**

$$\forall f \in \operatorname{Schwartz}\left(R, C\right),\; \forall h \in \operatorname{Schwartz}\left(R, C\right),\; \operatorname{embed}\left((f, h)\right) = (\operatorname{toLp}\left(f, 2, volume\right), \operatorname{toLp}\left(h, 2, volume\right))$$

*Formalization.* `D5/S3/Quantum/Analysis/GazeauNormalRealization.embed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Pierre Gazeau (2026). *Bi-Oriented Interlaced Matrix Multiplication and an Operator Factorisation of the Quantum Harmonic Oscillator*. URL: <https://arxiv.org/abs/2609.28511v1>.

*Commentary.*

ScalarL2 is Lp(C, 2, volume) on the real line, with its usual almost-everywhere equivalence classes. V is ScalarL2 times ScalarL2 and Core is Schwartz(R,C) times Schwartz(R,C). For c = (f,h), embed(c) takes both actual Schwartz functions to their Lebesgue L2 classes. This map is injective.

**Definition 1.2 (The full first-order source action).**

$$\forall f \in \operatorname{Schwartz}\left(R, C\right),\; \forall h \in \operatorname{Schwartz}\left(R, C\right),\; \operatorname{expression}\left((f, h)\right) = (xf+ih', -if'+xh)$$

*Formalization.* `D5/S3/Quantum/Analysis/GazeauNormalRealization.expression` (`✓ std3`).

*Citation.* Jean-Pierre Gazeau (2026). *Bi-Oriented Interlaced Matrix Multiplication and an Operator Factorisation of the Quantum Harmonic Oscillator*. URL: <https://arxiv.org/abs/2609.28511v1>.

*Commentary.*

On every Schwartz pair, expression(f,h) = (xf + i h', -i f' + xh). The coordinate multiplication is the genuine complex-linear map f(x) to x f(x), and the primes are real derivatives. The action is defined on all of Core.

**Definition 1.3 (Algebraic transport of the entire source graph).**

$$\operatorname{sourceGraph}\left(e\right) = \{(\operatorname{e}\left(\operatorname{embed}\left(c\right)\right), \operatorname{e}\left(\operatorname{embed}\left(\operatorname{expression}\left(c\right)\right)\right)) \mid c \in Core\}$$

*Formalization.* `D5/S3/Quantum/Analysis/GazeauNormalRealization.sourceGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jean-Pierre Gazeau (2026). *Bi-Oriented Interlaced Matrix Multiplication and an Operator Factorisation of the Quantum Harmonic Oscillator*. URL: <https://arxiv.org/abs/2609.28511v1>.

*Commentary.*

H carries the candidate Hilbert structure and e is any algebraic complex-linear equivalence from V to H. sourceGraph(e) contains the pair (e(embed(c)), e(embed(expression(c)))) for every c in Core. Continuity of e, equivalence to the standard L2 norm, and density of the transported Schwartz core are not assumed.

**Theorem 1.4 (All three adjoint alternatives are impossible).**

$$\forall H \in CompleteComplexHilbertSpace,\; \forall e \in \operatorname{ComplexLinearEquivalence}\left(V, H\right),\; \neg \left(\exists T \in \operatorname{ComplexLinearPartialOperator}\left(H, H\right),\; (\operatorname{sourceGraph}\left(e\right) \subseteq \operatorname{graph}\left(T\right)) \land ((\operatorname{Dense}\left(\operatorname{domain}\left(T\right)\right)) \land ((\operatorname{IsClosed}\left(T\right)) \land ((\operatorname{adjoint}\left(T\right) = T) \lor ((\operatorname{adjoint}\left(T\right) = -T) \lor (\forall x \in H,\; \forall z \in H,\; (\exists y \in H,\; ((x, y) \in \operatorname{graph}\left(T\right)) \land ((y, z) \in \operatorname{graph}\left(\operatorname{adjoint}\left(T\right)\right))) \Leftrightarrow (\exists y \in H,\; ((x, y) \in \operatorname{graph}\left(\operatorname{adjoint}\left(T\right)\right)) \land ((y, z) \in \operatorname{graph}\left(T\right))))))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GazeauNormalRealization.result` (`✓ std3`). ∎

*Resolves.* `Problems/gazeau-2026-problem-4-3-hilbert-realization` (refuted) by `D5/S3/Quantum/Analysis/GazeauNormalRealization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gazeau-2026-problem-4-3-hilbert-realization","declaration_gid":"D5/S3/Quantum/Analysis/GazeauNormalRealization.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jean-Pierre Gazeau (2026). *Bi-Oriented Interlaced Matrix Multiplication and an Operator Factorisation of the Quantum Harmonic Oscillator*. URL: <https://arxiv.org/abs/2609.28511v1>.

*Commentary.*

H is any complete complex Hilbert space. The partial operator T is complex-linear, its domain is dense in H, and its graph is closed in H times H. The expression adjoint(T) is its actual Hilbert adjoint, denoted Tstar in the explanation. Each existential intermediate vector below imposes the appropriate product domain, so the displayed relation equality is the full maximal-graph equality Tstar after T = T after Tstar. Equality Tstar = T or Tstar = -T includes equality of domains.

Take the actual Schwartz Gaussian g(x) = exp(-x squared / 2). Its derivative is -xg, and (xg)' = g - x squared g. Thus the core pairs cv = (g,-ig) and cw = (xg,-ixg) satisfy expression(cv) = 0 and expression(cw) = cv. The vector v = e(embed(cv)) is nonzero since g(0) = 1 and both embeddings are injective. Full source graph containment gives Tv = 0 and Tw = v.

In the normal branch, product-graph equality at (v,0) supplies Tstar v = a with a in the domain of T and Ta = 0. The actual adjoint identity gives inner(a,a) = inner(v,Ta) = 0, hence a = 0. Applying the identity at w gives inner(v,v) = inner(a,w) = 0, a contradiction. In the self-adjoint and skew-adjoint branches, the partial-map equality directly gives Tstar v = 0 and the same contradiction.

Every complete positive Hermitian metric on the fixed vector space V is represented by a type copy H and an algebraic equivalence e. A genuine self-adjoint or skew-adjoint graph closure retaining this source action would be such an extension and is therefore excluded. No arbitrary-metric closability or density of the original core is asserted. Problem 4.4, distributional operators, interlaced products and indefinite metrics remain outside this conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/GazeauNormalRealization.embed`
- Truth anchor: `D5/S3/Quantum/Analysis/GazeauNormalRealization.expression`
- Truth anchor: `D5/S3/Quantum/Analysis/GazeauNormalRealization.result`
- Truth anchor: `D5/S3/Quantum/Analysis/GazeauNormalRealization.sourceGraph`
- Dependency: [D5/S3/Quantum/Analysis/GaussianSchwartz](GaussianSchwartz.md)
