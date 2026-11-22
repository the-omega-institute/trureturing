# Crossed-module surface pasting

## Abstract

Peiffer interchange governs typed face pasting. A tetrahedral shell can have a nonidentity central obstruction.

A crossed module consists of a group homomorphism μ from H to G and an action of G on H by automorphisms. Equivariance says that μ sends the action by p to conjugation by p. The Peiffer identity says that the action by μ(h) is conjugation by h.

**Theorem 1.1 (The kernel is central).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (h: H), h \in \operatorname{ker}\left(X\right) \Rightarrow h \in \operatorname{center}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.ker_le_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If μ(h) is the identity, the Peiffer identity gives hkh⁻¹ = k for every k in H. Right multiplication by h gives commutativity with h.

**Theorem 1.2 (The face boundary equation).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (p: G), \forall (q: G), \forall (h: H), \operatorname{mu}\left(X, h\right) \cdot p = q \Leftrightarrow \operatorname{mu}\left(X, h\right) = q \cdot p^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.fake_flat_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Right multiplication by the inverse source path gives the fake-flatness equation. Right multiplication by the source path recovers the boundary equation.

Write v(h,k) for vertical pasting, with label kh, and m(h,k) for horizontal pasting, with label h times the action by the first source path on k. The letter ℓ denotes the label of a face. Equivariance gives the horizontal target path by carrying the second boundary through the first source path. The identity face i(X,p) has label 1 at both copies of path p.

**Theorem 1.3 (Vertical identity and associativity).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (p: G), \forall (q: G), \forall (r: G), \forall (s: G), \forall (h: \operatorname{Face}\left(X, p, q\right)), \forall (k: \operatorname{Face}\left(X, q, r\right)), \forall (l: \operatorname{Face}\left(X, r, s\right)), (\operatorname{v}\left(\operatorname{i}\left(X, p\right), h\right) = h) \land (\operatorname{v}\left(h, \operatorname{i}\left(X, q\right)\right) = h) \land \operatorname{v}\left(\operatorname{v}\left(h, k\right), l\right) = \operatorname{v}\left(h, \operatorname{v}\left(k, l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.vertical_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both identity laws follow from the unit in H. Associativity compares products of three labels in reverse traversal order.

**Theorem 1.4 (Horizontal identity and associativity).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (p: G), \forall (q: G), \forall (a: G), \forall (b: G), \forall (c: G), \forall (d: G), \forall (h: \operatorname{Face}\left(X, p, q\right)), \forall (k: \operatorname{Face}\left(X, a, b\right)), \forall (l: \operatorname{Face}\left(X, c, d\right)), (\operatorname{ell}\left(\operatorname{m}\left(\operatorname{i}\left(X, 1\right), h\right)\right) = \operatorname{ell}\left(h\right)) \land (\operatorname{ell}\left(\operatorname{m}\left(h, \operatorname{i}\left(X, 1\right)\right)\right) = \operatorname{ell}\left(h\right)) \land \operatorname{ell}\left(\operatorname{m}\left(\operatorname{m}\left(h, k\right), l\right)\right) = \operatorname{ell}\left(\operatorname{m}\left(h, \operatorname{m}\left(k, l\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.horizontal_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity and associativity follow because the action is a homomorphism into automorphisms. Group associativity identifies the endpoint products of the two triple pastings.

**Theorem 1.5 (Peiffer interchange).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (p: G), \forall (q: G), \forall (r: G), \forall (a: G), \forall (b: G), \forall (c: G), \forall (h: \operatorname{Face}\left(X, p, q\right)), \forall (k: \operatorname{Face}\left(X, a, b\right)), \forall (j: \operatorname{Face}\left(X, q, r\right)), \forall (l: \operatorname{Face}\left(X, b, c\right)), \operatorname{v}\left(\operatorname{m}\left(h, k\right), \operatorname{m}\left(j, l\right)\right) = \operatorname{m}\left(\operatorname{v}\left(h, j\right), \operatorname{v}\left(k, l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.interchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h from p to q, the relation q = μ(h)p gives (q acting on k')h = h(p acting on k'). Substitute this equality in the vertical paste of the two horizontal rows, and use multiplicativity of the action. The two results are faces with the same endpoints and the same label.

The face on ijk runs from edge gain gᵢₖ to the product gᵢⱼgⱼₖ. The left paste uses face 013 followed by face 123 whiskered by edge 01. Its label A is the product of the action by g₀₁ on h₁₂₃ and h₀₁₃. The right paste uses face 023 followed by face 012 whiskered by edge 23. Its label B is h₀₁₂h₀₂₃. Both run from g₀₃ to g₀₁(g₁₂g₂₃). Write Ω for AB⁻¹.

**Theorem 1.6 (The obstruction is in the kernel).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (T: \operatorname{Tetrahedron}\left(X\right)), \operatorname{Omega}\left(T\right) \in \operatorname{ker}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.obstruction_mem_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cancelling the common source in the two boundary equations gives μ(A) = μ(B). Applying μ to their ratio gives the identity.

**Theorem 1.7 (The obstruction is central).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (T: \operatorname{Tetrahedron}\left(X\right)), \operatorname{Omega}\left(T\right) \in \operatorname{center}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.obstruction_mem_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the central kernel property to the ratio.

**Theorem 1.8 (Triviality is equality of composite labels).**

$$\forall (u: \operatorname{Universe}), \forall (v: \operatorname{Universe}), \forall (H: \operatorname{Type}\left(u\right)), \forall (G: \operatorname{Type}\left(v\right)), [\operatorname{Group}\left(H\right)] [\operatorname{Group}\left(G\right)], \forall (X: \operatorname{CrossedModule}\left(H, G\right)), \forall (T: \operatorname{Tetrahedron}\left(X\right)), \operatorname{Omega}\left(T\right) = 1 \Leftrightarrow \operatorname{ell}\left(\operatorname{left}\left(T\right)\right) = \operatorname{ell}\left(\operatorname{right}\left(T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.obstruction_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the ratio equation by B on the right gives A = B. Substituting A = B gives the identity ratio.

**Theorem 1.9 (A quaternion shell with obstruction minus one).**

$$\exists (T: \operatorname{Tetrahedron}\left(\operatorname{q8CrossedModule}\right)), \operatorname{Omega}\left(T\right) = \operatorname{a}\left(2\right) \land \operatorname{Omega}\left(T\right) \neq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.q8_tetrahedron_nontrivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write a and x for the quaternion generators. The map to the Klein four group sends aⁱ to (0, i mod 2) and xaⁱ to (1, i mod 2). Conjugation descends to the quotient because its kernel consists of 1 and a², both central. On edges 01 and 12 use the images of a and x. Give every other edge gain 1. The faces 012, 013, 023 and 123 have labels xa, a, 1 and x. The resulting composites have labels ax = xa³ and xa. Their ratio is a², distinct from 1.

**Theorem 1.10 (Facewise fake flatness permits a nontrivial shell).**

$$\neg (\forall (T: \operatorname{Tetrahedron}\left(\operatorname{q8CrossedModule}\right)), \operatorname{Omega}\left(T\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four quaternion faces satisfy their boundary equations. The ratio of their composites is the central element a².

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.fake_flat_iff`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.horizontal_laws`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.interchange`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.ker_le_center`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.obstruction_eq_one_iff`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.obstruction_mem_center`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.obstruction_mem_ker`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.q8_tetrahedron_nontrivial`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.vertical_laws`
