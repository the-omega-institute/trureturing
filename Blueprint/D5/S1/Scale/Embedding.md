# Golden Real Embedding

## Abstract

The real embedding of golden integers is an injective ring homomorphism.

`D5/S1/Scale/Embedding` sends the golden integer $a + b \cdot \varphi$ to the real number with the same coordinate formula.

**Proposition 1.1 (Coordinate formula).**

$\forall x \in \operatorname{GoldenInt},\ \operatorname{embedding}(x)=x.a+x.b\varphi$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Embedding.embedding_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

$$
\operatorname{embedding}\left(a + b \cdot \varphi\right) = a + b \cdot \varphi
$$

## Quadratic relation

The defining identity makes the coordinate map multiplicative; $\psi$ denotes the conjugate root.

$$
\varphi^{2} = \varphi + 1
$$

$$
\psi = 1 - \varphi
$$

$$
\left\{\varphi, \psi\right\}
$$

**Theorem 1.2 (Injectivity).**

$\forall x,y \in \operatorname{GoldenInt},\ \operatorname{embedding}(x)=\operatorname{embedding}(y) \Rightarrow x=y$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Embedding.embedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coordinate collision with $b \ne 0$ would force the forbidden rational identity

$$
\varphi = \frac{-a}{b}
$$

## Norm recovery

**Theorem 1.3 (Embedding times conjugate).**

$\forall x \in \operatorname{GoldenInt},\ \operatorname{embedding}(x)\operatorname{embedding}(\operatorname{conj}(x))=\operatorname{norm}(x)$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Embedding.embedding_mul_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

$$
\operatorname{embedding}\left(x\right) \cdot \operatorname{embedding}\left(\operatorname{conj}\left(x\right)\right) = \operatorname{norm}\left(x\right)
$$

**Theorem 1.4 (Absolute norm relation).**

$\forall x \in \operatorname{GoldenInt},\ \lvert\operatorname{embedding}(x)\rvert\,\lvert\operatorname{embedding}(\operatorname{conj}(x))\rvert=\lvert\operatorname{norm}(x)\rvert$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Embedding.abs_embedding_mul_abs_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking absolute values gives the corresponding multiplicative relation.

$$
\left|\operatorname{embedding}\left(x\right)\right| \cdot \left|\operatorname{embedding}\left(\operatorname{conj}\left(x\right)\right)\right| = \left|\operatorname{norm}\left(x\right)\right|
$$

## References

- Truth anchor: `D5/S1/Scale/Embedding.abs_embedding_mul_abs_conj`
- Truth anchor: `D5/S1/Scale/Embedding.embedding_apply`
- Truth anchor: `D5/S1/Scale/Embedding.embedding_mul_conj`
- Truth anchor: `D5/S1/Scale/Embedding.embedding_injective`
- Dependency: [D5/S0/Carrier/Norm](../../S0/Carrier/Norm.md)
