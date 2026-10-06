# Ternary translation quadratic forms split into binary bilinear blocks

## Abstract

A binary quadratic form on functions over a ternary group, built from a graph and vertex translations, is linearly equivalent to a sum of binary bilinear blocks, one per pair of opposite nonzero characters.

**Definition 1.1 (The translation quadratic form).**

$$\forall N d: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{Z}/2\mathbb{Z}\right), \forall \delta: \operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}), \forall x: (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}) \to \operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}, \operatorname{F}\left(A, \delta, x\right) = \sum_{r, u < v} A(u, v) \times (x(r, u) \cdot x(r, v) + x(r + \delta(u), u) \cdot x(r + \delta(v), v))$$

*Formalization.* `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write ℤ/2ℤ for the binary field and (ℤ/3ℤ)^d, the functions Fin d → ℤ/3ℤ, for the ternary group. For any binary matrix A and a translation δ_u at each index u, the form sums over replicas r and indices u < v. It uses A_uv to weight the product at r and the product at r + δ_u and r + δ_v. For a graph adjacency matrix these are the two replica contributions of each edge; diagonal entries of A are unused.

**Definition 1.2 (The cut matrix of a character).**

$$\forall N d: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{Z}/2\mathbb{Z}\right), \forall \delta: \operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}), \forall t: (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}), \forall u v: \operatorname{Fin}\left(N\right), \operatorname{C}\left(A, \delta, t\right)(u, v) = \operatorname{if}\left(\sum_{i} t(i) \cdot \delta(u)(i) = \sum_{i} t(i) \cdot \delta(v)(i), 0, A(u, v)\right)$$

*Formalization.* `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a character t of the ternary group, C_t keeps the entries A_uv whose translations have different values under t and sets the others to zero.

**Theorem 1.3 (The block normal form).**

$$\forall N d: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{Z}/2\mathbb{Z}\right), (\forall u v: \operatorname{Fin}\left(N\right), A(u, v) = A(v, u)) \Rightarrow \forall \delta: \operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}), \forall P: \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z})\right), \neg (0 \in P) \Rightarrow (\forall t: (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}), t \neq 0 \Rightarrow (t \in P \Leftrightarrow \neg (-t \in P))) \Rightarrow \exists E: \operatorname{LinearEquiv}\left(\mathbb{Z}/2\mathbb{Z}, (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}) \to \operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}, (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}) \times (\{t: (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}) \mid t \in P\} \to ((\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}) \times (\operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z})))\right), \forall x: (\operatorname{Fin}\left(d\right) \to \mathbb{Z}/3\mathbb{Z}) \to \operatorname{Fin}\left(N\right) \to \mathbb{Z}/2\mathbb{Z}, \operatorname{F}\left(A, \delta, x\right) = \sum_{t \in P} \sum_{u,v} \operatorname{fst}\left(\operatorname{snd}\left(E(x)\right)(t)\right)(u) \cdot \operatorname{C}\left(A, \delta, t\right)(u, v) \cdot \operatorname{snd}\left(\operatorname{snd}\left(E(x)\right)(t)\right)(v)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.ternary_translation_quadratic_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be symmetric and let P omit zero and contain exactly one of t and −t for every nonzero character t. No restriction on the diagonal of A is needed: F ignores it and every C_t has zero diagonal. Encode x by its sums over replicas at each vertex and, for each t in P, by the two binary coordinates in the basis (1, ω) of the twisted Fourier coefficient χ_t(δ_u) times the transform of x at u, computed in the field with four elements. The first component of E(x) is the constant mode; fst(snd(E(x))(t)) and snd(snd(E(x))(t)) are the two vectors of the t block. The encoding is injective: the constant mode together with one mode from each pair of opposite characters determines every binary coefficient of x by Fourier inversion, because the transform at −t is the Frobenius conjugate of the transform at t. Hence it is a linear equivalence by counting. Expanding each edge term in Fourier modes, the two replica terms of an edge cancel in every mode t with t·δ_u = t·δ_v, since 1 + 1 = 0 in characteristic two, and the remaining cross terms over the pair {t, −t} are the binary bilinear form of C_t in the two coordinates of mode t.

## References

- Truth anchor: `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.C`
- Truth anchor: `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.F`
- Truth anchor: `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.ternary_translation_quadratic_normal_form`
