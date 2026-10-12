# A hidden central direction refutes Heib–Bruschi Conjecture 80

## Abstract

A hidden central direction refutes Heib–Bruschi Conjecture 80.

**Definition 1.1 (Conjecture 80 over a field).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)], \operatorname{conjecture80Over}\left(K\right) \Leftrightarrow (\forall L: Type, [\operatorname{LieRing}\left(L\right)], [\operatorname{LieAlgebra}\left(K, L\right)], \forall n: \mathbb{N}, \forall b: \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, L\right), \operatorname{IsAdmissible}\left(b\right) \Rightarrow \operatorname{center}\left(K, L\right) \neq \perp \Rightarrow (\exists W: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{Nonempty}\left(W\right) \land W \neq \operatorname{univ}\left(\right) \land \operatorname{IdealGraphProperty}\left(b, W\right) \land (\exists I: \operatorname{LieIdeal}\left(K, L\right), \operatorname{toSubmodule}\left(I\right) = \operatorname{span}\left(K, \operatorname{image}\left(b, W\right)\right) \land \operatorname{IsSolvable}\left(I\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.conjecture80Over` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

For each Lie algebra over K and each admissible finite basis b, a nonzero center is required to imply that a proper nonempty subset W of the basis indices has the ideal-graph-property and that the span of b(W) is a solvable Lie ideal. The graph belongs to the given basis: the assertion quantifies over every admissible basis.

**Definition 1.2 (Conjecture 80).**

$$claim \Leftrightarrow (\forall K: Type, [\operatorname{Field}\left(K\right)], \operatorname{conjecture80Over}\left(K\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.claim` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

Conjecture 80 of Heib and Bruschi, arXiv:2601.16161v1, §IV.D, p. 46: "Let g be a finite-dimensional minimal-graph-admissible Lie algebra associated with the minimal graph G(V,E). If g has a non-zero center Z(g), then there exists a proper non-empty subset W⊊V that satisfies the ideal-graph-property and spans a solvable ideal of g." The paper's convention "We denote any field with the symbol 𝔽" makes this an assertion over every field K.

**Theorem 1.3 (Conjecture 80 is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/heib-bruschi-2026-conjecture-80-hidden-center-refutation` (refuted) by `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"heib-bruschi-2026-conjecture-80-hidden-center-refutation","declaration_gid":"D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

For any field K, give K⁴ the bracket [u,v]=(b(r+s)−(c+d)q, (c+d)p−a(r+s), aq−bp, 0), where u=(a,b,c,d) and v=(p,q,r,s). The map u↦((a,b,c+d),d) identifies this with the cross-product Lie algebra K³ together with a central copy of K. Its standard basis satisfies [e₁,e₂]=e₃, [e₂,e₃]=e₁, [e₃,e₁]=e₂, [e₁,e₄]=−e₂, [e₂,e₄]=e₁ and [e₃,e₄]=0, so it is admissible, while e₄−e₃ is central and nonzero. Every nonempty vertex subset with the ideal-graph-property contains e₁,e₂,e₃; the only proper one is {e₁,e₂,e₃}. Its span I satisfies [I,I]=I≠0 and is therefore not solvable. These identities hold in every characteristic. Taking K to be the rational numbers contradicts the assertion over every field.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.conjecture80Over`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.result`
- Dependency: [D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation](HeibBruschiCenterlessIdealGraphRefutation.md)
