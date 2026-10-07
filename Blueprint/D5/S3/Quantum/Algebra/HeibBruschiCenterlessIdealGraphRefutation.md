# The affine Lie algebra refutes Heib–Bruschi Conjecture 83

## Abstract

The two-dimensional affine Lie algebra refutes Heib–Bruschi Conjecture 83 over every field.

**Definition 1.1 (Minimal-graph-admissible bases).**

$$\forall K L: Type, [\operatorname{Field}\left(K\right)], [\operatorname{LieRing}\left(L\right)], [\operatorname{LieAlgebra}\left(K, L\right)], \forall n: \mathbb{N}, \forall b: \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, L\right), \operatorname{IsAdmissible}\left(b\right) \Leftrightarrow (\exists \alpha: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right) \to K, \exists \delta: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right) \to \operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right), (\forall j k: \operatorname{Fin}\left(n\right), \alpha(j, k) = -\alpha(k, j)) \land (\forall j k: \operatorname{Fin}\left(n\right), \delta(j, k) = \delta(k, j)) \land (\forall j k: \operatorname{Fin}\left(n\right), (\delta(j, k) = none \Leftrightarrow \alpha(j, k) = 0)) \land (\forall j k: \operatorname{Fin}\left(n\right), [b(j), b(k)] = \alpha(j, k) \cdot \operatorname{elim}\left(\delta(j, k), 0, b\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.IsAdmissible` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

Definition 16 of arXiv:2601.16161v1 asks for a basis with "[x_j,x_k]=α_jk x_δ(j,k)", α antisymmetric and δ symmetric, and sets "δ(j,k):=0 whenever α_jk=0" with "x_0:=0". The index none plays the role of 0 and elim(δ(j,k), 0, b) is x_δ(j,k).

**Definition 1.2 (Edges of the minimal graph).**

$$\forall K L: Type, [\operatorname{Field}\left(K\right)], [\operatorname{LieRing}\left(L\right)], [\operatorname{LieAlgebra}\left(K, L\right)], \forall n: \mathbb{N}, \forall b: \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, L\right), \forall j k l: \operatorname{Fin}\left(n\right), \operatorname{Edge}\left(b, j, k, l\right) \Leftrightarrow (\exists \kappa: K, \kappa \neq 0 \land [b(j), b(k)] = \kappa \cdot b(l))$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.Edge` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

Algorithm 1 draws an edge from v_j to v_ℓ labelled v_k when "[x_j,x_k]∝x_ℓ", and x∝y means x=κy with κ a nonzero field element. A minimal graph is built from a basis, so its vertices are the indices of the basis.

**Definition 1.3 (The ideal-graph-property).**

$$\forall K L: Type, [\operatorname{Field}\left(K\right)], [\operatorname{LieRing}\left(L\right)], [\operatorname{LieAlgebra}\left(K, L\right)], \forall n: \mathbb{N}, \forall b: \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, L\right), \forall W: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{IdealGraphProperty}\left(b, W\right) \Leftrightarrow (\forall j k l: \operatorname{Fin}\left(n\right), \operatorname{Edge}\left(b, j, k, l\right) \Rightarrow j \in W \Rightarrow l \in W)$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.IdealGraphProperty` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

Definition 75: "A subset W⊆V is said to satisfy the ideal-graph-property if and only if no edge e∈E points from a vertex w∈W to a vertex v∈V∖W." Edges with any label count.

**Definition 1.4 (A proper subset with the ideal-graph-property).**

$$\forall K L: Type, [\operatorname{Field}\left(K\right)], [\operatorname{LieRing}\left(L\right)], [\operatorname{LieAlgebra}\left(K, L\right)], \forall n: \mathbb{N}, \forall b: \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, L\right), \operatorname{HasProperIdealGraphSubset}\left(b\right) \Leftrightarrow (\exists W: \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{Nonempty}\left(W\right) \land W \neq univ \land \operatorname{IdealGraphProperty}\left(b, W\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.HasProperIdealGraphSubset` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

This is the negation of condition (i) of Conjecture 83: some proper non-empty vertex subset has the ideal-graph-property.

**Definition 1.5 (Conjecture 83 over a field).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)], \operatorname{conjectureOver}\left(K\right) \Leftrightarrow (\forall L: Type, [\operatorname{LieRing}\left(L\right)], [\operatorname{LieAlgebra}\left(K, L\right)], \forall n: \mathbb{N}, \forall b: \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), K, L\right), \operatorname{IsAdmissible}\left(b\right) \Rightarrow \operatorname{center}\left(K, L\right) = \perp \Rightarrow (\neg \operatorname{HasProperIdealGraphSubset}\left(b\right) \lor (\exists J: Type, \exists inst: \operatorname{DecidableEq}\left(J\right), \exists I: J \to \operatorname{LieIdeal}\left(K, L\right), \operatorname{IsInternal}\left(\lambda j \mapsto \operatorname{toSubmodule}\left(I(j)\right)\right) \land (\forall j: J, \operatorname{center}\left(K, I(j)\right) = \perp \land (\forall m: \mathbb{N}, \forall c: \operatorname{Basis}\left(\operatorname{Fin}\left(m\right), K, I(j)\right), \operatorname{IsAdmissible}\left(c\right) \Rightarrow \neg \operatorname{HasProperIdealGraphSubset}\left(c\right))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.conjectureOver` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

Conjecture 83 (§IV.D): for a minimal-graph-admissible Lie algebra with trivial center, either (i) no proper non-empty vertex subset has the ideal-graph-property, or (ii) the algebra is a direct sum of components with trivial center whose every minimal graph has no such subset. The direct sum is an internal direct sum of ideals I(j) indexed by an arbitrary type J, which is a Lie-algebra direct sum because brackets between different ideals lie in their zero intersection; every admissible basis c of a component gives one of its minimal graphs.

**Definition 1.6 (Conjecture 83).**

$$claim \Leftrightarrow (\forall K: Type, [\operatorname{Field}\left(K\right)], \operatorname{conjectureOver}\left(K\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.claim` (`✓ std3`).

*Citation.* T. Heib; D. E. Bruschi (2026). *On the structural properties of Lie algebras via associated labeled directed graphs*. DOI: [10.48550/arXiv.2601.16161](https://doi.org/10.48550/arXiv.2601.16161). URL: <https://arxiv.org/abs/2601.16161v1>.

*Commentary.*

The paper denotes "any field" by 𝔽, so the conjecture is read over every field K.

**Theorem 1.7 (Conjecture 83 fails over every field).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)], \neg \operatorname{conjectureOver}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.conjecture_fails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A=K×K with bracket [(a,b),(c,d)]=(0,ad−cb) and basis X=(1,0), Y=(0,1), so [X,Y]=Y. The basis is admissible with α(0,1)=1, α(1,0)=−1 and δ(0,1)=δ(1,0)=1. The center is zero since [aX+bY,X]=−bY and [aX+bY,Y]=aY. The singleton {1} is proper and non-empty, and the only edge leaving Y comes from [Y,X]=−Y and returns to Y, so condition (i) fails. Every nonzero ideal contains Y, hence two different components of an internal direct sum cannot both be nonzero; the one nonzero component is all of A, and the basis transported to it keeps the subset {1}, so condition (ii) fails.

**Theorem 1.8 (Conjecture 83 is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/heib-bruschi-2026-conjecture-83-affine-refutation` (refuted) by `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"heib-bruschi-2026-conjecture-83-affine-refutation","declaration_gid":"D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Specializing the previous theorem to the rational numbers refutes the conjecture as stated for every field.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.Edge`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.HasProperIdealGraphSubset`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.IdealGraphProperty`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.IsAdmissible`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.conjectureOver`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.conjecture_fails`
- Truth anchor: `D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.result`
