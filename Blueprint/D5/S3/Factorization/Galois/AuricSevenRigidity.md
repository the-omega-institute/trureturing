# The zero-product tensor endpoint

## Abstract

The zero-product tensor endpoint forces homothety of two actual field spans.

**Theorem 1.1 (Zero-product tensor homothety).**

$$\forall (F: Type*), \forall (D: Type*), [\operatorname{Field}\left(F\right)] [\operatorname{Field}\left(D\right)] [\operatorname{Algebra}\left(F, D\right)] \forall (u1: D), \forall (u2: D), \forall (u3: D), \forall (p: D), \forall (q: D), \forall (s: D), ((u1 \ne 0) \land ((s \ne 0) \land ((u1 \cdot p = u3 \cdot s) \land (u1 \cdot q = -u2 \cdot s)))) \Rightarrow (\operatorname{Submodule}.\operatorname{span}\left(F, \{p, q, s\}\right) = \operatorname{Submodule}.\operatorname{map}\left(\operatorname{LinearMap}.\operatorname{mulLeft}\left(F, s / u1\right), \operatorname{Submodule}.\operatorname{span}\left(F, \{u1, u2, u3\}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/AuricSevenRigidity.zero_product_tensor_homothety` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fields F and D with an F-algebra structure, the three actual zero-product identities u₁p=u₃s and u₁q=−u₂s, with u₁ and s nonzero, identify the span of p,q,s with the image of the span of u₁,u₂,u₃ under multiplication by the original element s/u₁. This is the endpoint calculation used after the adjugate coefficient comparison; the preceding degree-seven contraction classification remains a separate obligation of the full source lemma.

**Theorem 1.2 (Nonzero homothety witness).**

$$\forall (F: Type*), \forall (D: Type*), [\operatorname{Field}\left(F\right)] [\operatorname{Field}\left(D\right)] [\operatorname{Algebra}\left(F, D\right)] \forall (u1: D), \forall (u2: D), \forall (u3: D), \forall (p: D), \forall (q: D), \forall (s: D), ((u1 \ne 0) \land ((s \ne 0) \land ((u1 \cdot p = u3 \cdot s) \land (u1 \cdot q = -u2 \cdot s)))) \Rightarrow (\exists (gamma: D), (gamma \ne 0) \land (\operatorname{Submodule}.\operatorname{span}\left(F, \{p, q, s\}\right) = \operatorname{Submodule}.\operatorname{map}\left(\operatorname{LinearMap}.\operatorname{mulLeft}\left(F, gamma\right), \operatorname{Submodule}.\operatorname{span}\left(F, \{u1, u2, u3\}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/AuricSevenRigidity.zero_product_tensor_homothety_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same calculation packages the multiplier as an explicit nonzero element of D. This declaration is a consumed witness for the preceding endpoint theorem, rather than an independent classification claim.

## References

- Truth anchor: `D5/S3/Factorization/Galois/AuricSevenRigidity.zero_product_tensor_homothety`
- Truth anchor: `D5/S3/Factorization/Galois/AuricSevenRigidity.zero_product_tensor_homothety_nonzero`
