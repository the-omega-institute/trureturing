# Bilinear coordinates for a ternary translation form

## Abstract

Translation on a ternary group pairs opposite Fourier modes. A symmetric binary quadratic form consequently decomposes into bilinear blocks over ℤ/2ℤ.

**Definition 1.1 (The translation quadratic form).**

$$\forall (N : \mathbb{N}), \forall (d : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \forall (\delta : (\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right)))), \forall (x : ((\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right)) \to (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))), \operatorname{F}\left(A, \delta, x\right) = \sum_{(r : (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right)))} \sum_{(u : \operatorname{Fin}\left(N\right))} \sum_{(v : \operatorname{Fin}\left(N\right))} \operatorname{ite}\left(u < v, \operatorname{A}\left(u, v\right) \cdot (\operatorname{x}\left(r, u\right) \cdot \operatorname{x}\left(r, v\right) + \operatorname{x}\left((r + \delta(u)), u\right) \cdot \operatorname{x}\left((r + \delta(v)), v\right)), 0\right)$$

*Formalization.* `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The variables are binary configurations indexed by the group Fin d → ℤ/3ℤ. For each ordered edge u < v, the form adds the original edge product to the product translated separately by δ(u) and δ(v). All sums and products in this definition take values in ℤ/2ℤ.

**Definition 1.2 (The character separation matrix).**

$$\forall (N : \mathbb{N}), \forall (d : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), \forall (\delta : (\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right)))), \forall (t : (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right))), \operatorname{C}\left(A, \delta, t\right) = (u : \operatorname{Fin}\left(N\right)) (v : \operatorname{Fin}\left(N\right)) \mapsto \operatorname{ite}\left(\sum_{(i : \operatorname{Fin}\left(d\right))} \operatorname{t}\left(i\right) \cdot \delta(u, i) = \sum_{(i : \operatorname{Fin}\left(d\right))} \operatorname{t}\left(i\right) \cdot \delta(v, i), 0, \operatorname{A}\left(u, v\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix keeps A(u,v) when the two ternary dot products differ and sets the entry to zero when they agree. Thus a character measures the separation of the two translation vectors.

**Theorem 1.3 (A linear equivalence to independent blocks).**

$$\forall (N : \mathbb{N}), \forall (d : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \operatorname{ZMod}\left(2\right)\right)), (\forall (u : \operatorname{Fin}\left(N\right)), \forall (v : \operatorname{Fin}\left(N\right)), \operatorname{A}\left(u, v\right) = \operatorname{A}\left(v, u\right)) \Rightarrow (\forall (\delta : (\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right)))), \forall (P : \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right))\right)), \neg (0 \in P) \Rightarrow ((\forall (t : (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right))), t \neq 0 \Rightarrow ((t \in P \Leftrightarrow \neg (-t \in P)))) \Rightarrow (\exists (E : \operatorname{LinearEquiv}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right)) \to (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right))), ((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)) \times (\{(t : (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right))) \mid t \in P\} \to ((\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))))\right)), \forall (x : ((\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right)) \to (\operatorname{Fin}\left(N\right) \to \operatorname{ZMod}\left(2\right)))), \operatorname{F}\left(A, \delta, x\right) = \sum_{(t : \{(t : (\operatorname{Fin}\left(d\right) \to \operatorname{ZMod}\left(3\right))) \mid t \in P\})} \sum_{(u : \operatorname{Fin}\left(N\right))} \sum_{(v : \operatorname{Fin}\left(N\right))} ((\operatorname{E}\left(x\right)).2(t)).1(u) \cdot \operatorname{C}\left(A, \delta, (t).val\right)(u, v) \cdot ((\operatorname{E}\left(x\right)).2(t)).2(v))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.ternary_translation_quadratic_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that A is symmetric and that P contains exactly one element from every opposite pair of nonzero modes. The ℤ/2ℤ-linear equivalence E has one constant-mode vector and a pair of binary vectors for each representative. The displayed sum uses precisely the first and second vectors of that pair. Fourier inversion over ℤ/2ℤ[ω], where ω² + ω + 1 = 0, constructs the equivalence; opposite modes are conjugate, and their cross terms give the bilinear blocks C(A,δ,t). No condition on the diagonal of A is required.

## References

- Truth anchor: `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.C`
- Truth anchor: `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.F`
- Truth anchor: `D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.ternary_translation_quadratic_normal_form`
