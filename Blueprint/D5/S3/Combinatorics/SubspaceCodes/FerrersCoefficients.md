# Coefficient recovery and support

## Abstract

The coefficients recover the full parameter tuple and enforce the two support cuts.

**Definition 1.1 (Parameter space).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] \forall K \in \operatorname{IntermediateField}\left(F, E\right),\; \forall L \in \operatorname{IntermediateField}\left(F, E\right),\; \operatorname{Params}\left(K, L\right) = L \times L \times L \times L \times K$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.Params` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is associated to the right. Each factor is the carrier of the corresponding intermediate field.

**Definition 1.2 (Linear coefficient map).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] \forall K \in \operatorname{IntermediateField}\left(F, E\right),\; \forall L \in \operatorname{IntermediateField}\left(F, E\right),\; \forall b \in E,\; \forall c \in E,\; \forall u \in L,\; \forall v \in L,\; \forall w \in L,\; \forall l \in L,\; \forall k \in K,\; (\left(paramCoefficients_{K,L}\right)\left(b, c\right) : \operatorname{LinearMap}\left(F, \operatorname{Params}\left(K, L\right), \operatorname{Fin}\left(4\right) \to E\right))\left((u, v, w, l, k)\right) = [(u : E) - (b^{\operatorname{card}\left(F\right)^{3}} - b)^{-1} \cdot ((l : E) + c \cdot (k : E) - b \cdot (u : E)), (v : E), (w : E), (b^{\operatorname{card}\left(F\right)^{3}} - b)^{-1} \cdot ((l : E) + c \cdot (k : E) - b \cdot (u : E))]$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output vector is indexed in order from zero through three. Field inversion is total, so the map is defined even when the determinant vanishes.

**Theorem 1.3 (Recovery of the five parameters).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] \forall K \in \operatorname{IntermediateField}\left(F, E\right),\; \forall L \in \operatorname{IntermediateField}\left(F, E\right),\; \forall b \in E,\; (b^{\operatorname{card}\left(F\right)^{3}} - b \ne 0) \Rightarrow (\forall B \in \operatorname{Basis}\left(\operatorname{Fin}\left(4\right), K, E\right),\; (K \le L) \Rightarrow ((\operatorname{flag}\left(B, 2\right) = \operatorname{toSubmodule}\left(\operatorname{toSubalgebra}\left(\operatorname{extendScalars}\left(K, L\right)\right)\right)) \Rightarrow (\operatorname{Injective}\left(\left(paramCoefficients_{K,L}\right)\left(b, B\left(2\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate along the third basis vector separates the last two parameters when the first two basis vectors span L over K.

**Theorem 1.4 (Evaluation on the first input block).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] [\operatorname{Finite}\left(E\right)] \forall K \in \operatorname{IntermediateField}\left(F, E\right),\; \forall L \in \operatorname{IntermediateField}\left(F, E\right),\; (\operatorname{finrank}\left(F, K\right) = 3) \Rightarrow (\forall b \in E,\; \forall c \in E,\; \forall p \in \operatorname{Params}\left(K, L\right),\; \forall x \in K,\; \operatorname{evaluateLinearized}\left(F, E, \left(paramCoefficients_{K,L}\right)\left(b, c\right)\left(p\right)\right)\left((x : E)\right) = (p.1 : E) \cdot (x : E) + (p.2.1 : E) \cdot (x : E)^{\operatorname{card}\left(F\right)} + (p.2.2.1 : E) \cdot (x : E)^{\operatorname{card}\left(F\right)^{2}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree-three hypothesis makes the third Frobenius iterate act as the identity on K.

**Theorem 1.5 (Evaluation on the second input block).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] \forall E \in Type,\; [\operatorname{Field}\left(E\right)] [\operatorname{Algebra}\left(F, E\right)] [\operatorname{Finite}\left(E\right)] \forall K \in \operatorname{IntermediateField}\left(F, E\right),\; \forall L \in \operatorname{IntermediateField}\left(F, E\right),\; (\operatorname{finrank}\left(F, K\right) = 3) \Rightarrow (\forall b \in E,\; \forall c \in E,\; (b^{\operatorname{card}\left(F\right)^{3}} - b \ne 0) \Rightarrow (\forall p \in \operatorname{Params}\left(K, L\right),\; \forall x \in K,\; \operatorname{evaluateLinearized}\left(F, E, \left(paramCoefficients_{K,L}\right)\left(b, c\right)\left(p\right)\right)\left(b \cdot (x : E)\right) = ((p.2.2.2.1 : E) + c \cdot (p.2.2.2.2 : E)) \cdot (x : E) + (p.2.1 : E) \cdot (b \cdot (x : E))^{\operatorname{card}\left(F\right)} + (p.2.2.1 : E) \cdot (b \cdot (x : E))^{\operatorname{card}\left(F\right)^{2}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_bK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating on b times K uses the nonzero determinant to recover the coefficient of x from the last two parameters.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.Params`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_K`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.evaluation_on_bK`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients.paramCoefficients_injective`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial](FerrersPolynomial.md)
