# Walk Formula Algebra

## Abstract

Isolate the alternating-list and endpoint-translation algebra behind the W3 walk expression.

This module records four algebraic laws with all structural premises explicit. It does not prove the BHK theorem, its finite certificates, or the canonical endpoint divisibility premise, and it does not identify any word, column, or Dedekind walk with the displayed expressions. The endpoint integrality theorem is only a conditional corollary and does not discharge the endpoint-translation-integrality residual.

**Theorem 1.1 (Concatenation carries the parity sign).**

$$\forall x,y\in\operatorname{List}(\mathbb{Z}),\ \operatorname{alt}(\operatorname{append}(x,y))=\operatorname{alt}(x)+(-1)^{\operatorname{length}(x)}\operatorname{alt}(y)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/WalkFormula.alternating_walk_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Concatenating two integer coefficient lists adds the second alternating walk with sign determined by the length of the first list. No continued-fraction normalization or orbit interpretation is inferred.

**Theorem 1.2 (Reversal carries the length-parity sign).**

$$\forall x\in\operatorname{List}(\mathbb{Z}),\ \operatorname{alt}(\operatorname{reverse}(x))=(-1)^{\operatorname{length}(x)+1}\operatorname{alt}(x)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/WalkFormula.alternating_walk_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal list reversal multiplies the alternating walk by minus one to the length-plus-one power. The theorem does not identify reversal with a fixed-point branch or an inverse orbit.

**Theorem 1.3 (An explicit endpoint multiple gives an integral correction).**

$$\forall e,e',c,t\in\mathbb{Z},\ c\neq 0 \land e-e'=ct \Rightarrow \frac{[e-e']_{\mathbb{Q}}}{[c]_{\mathbb{Q}}}=[t]_{\mathbb{Q}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/WalkFormula.endpoint_correction_is_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When an integer endpoint difference is explicitly equal to a nonzero denominator times an integer translation, its rational quotient is that integer. This is only a conditional corollary and does not discharge the endpoint-translation-integrality residual; the canonical endpoint divisibility witness remains a separate semantic obligation.

**Theorem 1.4 (Endpoint translation is exactly covariant).**

$$\forall a,e,e',c\in\mathbb{Q},\ \forall t\in\mathbb{Z},\ c\neq 0 \Rightarrow 3+a+\frac{(e+c[t]_{\mathbb{Q}})-e'}{c}=\left(3+a+\frac{e-e'}{c}\right)+[t]_{\mathbb{Q}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding an integral denominator multiple to the first endpoint adds exactly that integer to the rational W3 expression. This algebraic covariance does not assert a BHK or three-walk semantic identification.

## References

- Truth anchor: `D5/S1/Phase/WalkFormula.alternating_walk_append`
- Truth anchor: `D5/S1/Phase/WalkFormula.alternating_walk_reverse`
- Truth anchor: `D5/S1/Phase/WalkFormula.endpoint_correction_is_integer`
- Truth anchor: `D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation`
