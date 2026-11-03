# Infinitely many extreme classes in matrix D-majorization

## Abstract

A pure qubit has infinitely many extreme D-majorization classes under unitaries commuting with a positive diagonal D.

**Definition 1.1 (Matrix D-majorization).**

$$\forall (n: \mathbb{N}), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude.DMajorizedBy}\left(d, x, a\right)) \Leftrightarrow (\exists (t: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP}\left(t\right)) \land ((t\left(a\right) = x) \land (t\left(\operatorname{Matrix.diagonal}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Complex.ofReal}\left(d\left(i\right)\right))\right)\right) = \operatorname{Matrix.diagonal}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Complex.ofReal}\left(d\left(i\right)\right))\right)))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.DMajorizedBy` (`✓ std3`).

*Citation.* Frederik vom Ende (2022). *Strict positivity and D-majorization*. DOI: [10.1080/03081087.2020.1860887](https://doi.org/10.1080/03081087.2020.1860887). URL: <https://arxiv.org/abs/2004.05613v4>.

*Commentary.*

The matrix x is D-majorized by a when a completely positive, trace-preserving complex linear map t sends a to x and fixes the diagonal matrix with entries d(i). MatrixMap is the space of complex linear maps on these square matrices, and IsCPTP requires complete positivity and preservation of the trace of every input matrix. Each real entry d(i) is included in the complex numbers by Complex.ofReal before forming the diagonal. For strictly positive d this is Definition defi_matrix_D_maj in Strict positivity and D-majorization, TeX lines 466–469. The displayed predicate also makes sense for arbitrary real d; it imposes no positivity hypothesis.

**Definition 1.2 (The matrices reachable from a).**

$$\forall (n: \mathbb{N}), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude.majorizationSet}\left(d, a\right): \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)) = \{(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)) \mid \operatorname{D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude.DMajorizedBy}\left(d, x, a\right)\})))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.majorizationSet` (`✓ std3`).

*Citation.* Frederik vom Ende (2022). *Strict positivity and D-majorization*. DOI: [10.1080/03081087.2020.1860887](https://doi.org/10.1080/03081087.2020.1860887). URL: <https://arxiv.org/abs/2004.05613v4>.

*Commentary.*

The majorization set consists of all matrices x that are D-majorized by a. This is the singleton-input case M_D(a) of equation eq:def_MD, TeX lines 926–932. The definition allows every natural dimension n and every initial complex matrix a.

**Definition 1.3 (Finitely many extreme unitary classes).**

$$(\operatorname{D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < d\left(i\right))) \Rightarrow (\forall (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\exists (f: \operatorname{Finset}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)\right)), (\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((x \in \operatorname{Set.extremePoints}\left(\mathbb{R}, \operatorname{D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude.majorizationSet}\left(d, a\right)\right)) \Rightarrow (\exists (y: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((y \in f) \land (\exists (u: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((u \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(n\right), \mathbb{C}\right)) \land (((u) \cdot (\operatorname{Matrix.diagonal}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Complex.ofReal}\left(d\left(i\right)\right))\right)) = (\operatorname{Matrix.diagonal}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Complex.ofReal}\left(d\left(i\right)\right))\right)) \cdot (u)) \land (x = ((u) \cdot (y)) \cdot (\operatorname{star}\left(u\right)))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Strict positivity and D-majorization*. DOI: [10.1080/03081087.2020.1860887](https://doi.org/10.1080/03081087.2020.1860887). URL: <https://arxiv.org/abs/2004.05613v4>.

*Commentary.*

For every natural n, strictly positive real vector d and complex matrix a, the assertion asks for a finite set f representing every real extreme point of M_D(a) by conjugation with a unitary matrix u commuting with D. The finite set f is a set of ambient matrices. The real scalar field in Set.extremePoints specifies real convex combinations. This expresses the finiteness question in the Conclusion and Outlook, TeX lines 1058–1064. The quantifier includes n equal to zero; no positive-dimension assumption is added.

**Theorem 1.4 (A qubit with infinitely many extreme classes).**

$$\neg (\operatorname{D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.result` (`✓ std3`). ∎

*Resolves.* `Problems/vom-ende-2022-d-majorization-extreme-class-infinitude` (refuted) by `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vom-ende-2022-d-majorization-extreme-class-infinitude","declaration_gid":"D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Strict positivity and D-majorization*. DOI: [10.1080/03081087.2020.1860887](https://doi.org/10.1080/03081087.2020.1860887). URL: <https://arxiv.org/abs/2004.05613v4>.

*Commentary.*

Take n = 2, d = (1/3, 2/3), D = diag(1/3, 2/3) and A = diag(1, 0). For each natural m, including zero, put h = m² + 1 and Pₘ = (1/h)[[m², m], [m, 1]]. The denominator h is nonzero. Let r = 1/√h and s = 1/√2, with these real numbers regarded as complex scalars. Use the three Kraus matrices K₀ = [[mr, 0], [r, 0]], K₁ = [[0, rs], [0, −mrs]] and K₂ = [[0, 0], [0, s]]. Their map Tₘ(X) = ∑ⱼ KⱼXKⱼ* satisfies Tₘ(X) = X₀₀Pₘ + (X₁₁/2)(I − Pₘ + diag(0, 1)), using r² = 1/h and s² = 1/2.

The Kraus representation makes Tₘ completely positive. The identity tr(Pₘ) = 1 and the displayed action give tr(Tₘ(X)) = X₀₀ + X₁₁ = tr(X), so it is trace preserving. Substituting A gives Tₘ(A) = Pₘ, and substituting D gives Tₘ(D) = D. Thus every Pₘ lies in M_D(A). Every matrix x in M_D(A) is positive semidefinite and has trace one: a channel taking A to x preserves positivity and trace.

A positive semidefinite matrix x of trace one that annihilates the vector (1, −m) must equal Pₘ. Indeed, the two coordinates of x(1, −m) = 0 and Hermitian symmetry give x₀₁ = mx₁₁ and x₀₀ = m²x₁₁. The trace condition then gives hx₁₁ = 1, which determines all four entries.

To prove extremality, suppose Pₘ = rx + sy with x, y in M_D(A), real r, s > 0 and r + s = 1. Set v = (1, −m). Direct multiplication gives Pₘv = 0. Consequently r(v*xv) + s(v*yv) = 0. Both quadratic forms are nonnegative, so v*xv = 0. For a positive semidefinite matrix this implies xv = 0. The preceding trace-one calculation gives x = Pₘ, which is the extreme-point condition. Hence every Pₘ is a real extreme point of M_D(A).

For any unitary u commuting with D and any matrix y, tr(Duyu*) = tr(Dy): commute u past D and use invariance of trace under unitary conjugation. On the matrices above this invariant is tr(DPₘ) = (m² + 2)/(3(m² + 1)). Equality of its values at m and k, after clearing the nonzero denominators, gives m² = k². Since m and k are natural numbers, m = k. Thus the invariant is injective on this family.

Suppose the finiteness assertion holds and apply it to this d and A. It supplies a finite set f, and for each m a matrix y(m) in f and a unitary u(m) commuting with D such that Pₘ = u(m)y(m)u(m)*. If y(m) = y(k), trace invariance gives tr(DPₘ) = tr(DPₖ), hence m = k. The function y is therefore injective. Its preimage of the finite set f is finite, but contains every natural number, contradicting infinitude of the natural numbers.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.DMajorizedBy`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.majorizationSet`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](PositiveFilterTransposeRefutation.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
