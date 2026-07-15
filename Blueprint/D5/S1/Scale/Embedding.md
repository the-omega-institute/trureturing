# Golden Real Embedding

`D5/S1/Scale/Embedding` sends the golden integer $a + b \cdot \varphi$ to the real number with the same coordinate formula.

## Proposition: Coordinate formula

Provenance: `repo-derived`

Statement: `D5/S1/Scale/Embedding.embedding_apply` `✓ std3`

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

## Theorem: Injectivity

Provenance: `repo-derived`

Statement: `D5/S1/Scale/Embedding.embedding_injective` `✓ std3`

A coordinate collision with $b \ne 0$ would force the forbidden rational identity

$$
\varphi = \frac{-a}{b}
$$

## Norm recovery

### Theorem: Embedding times conjugate

Provenance: `repo-derived`

Statement: `D5/S1/Scale/Embedding.embedding_mul_conj` `✓ std3`

$$
\operatorname{embedding}\left(x\right) \cdot \operatorname{embedding}\left(\operatorname{conj}\left(x\right)\right) = \operatorname{norm}\left(x\right)
$$

### Theorem: Absolute norm relation

Provenance: `repo-derived`

Statement: `D5/S1/Scale/Embedding.abs_embedding_mul_abs_conj` `✓ std3`

Taking absolute values gives the corresponding multiplicative relation.

$$
\left|\operatorname{embedding}\left(x\right)\right| \cdot \left|\operatorname{embedding}\left(\operatorname{conj}\left(x\right)\right)\right| = \left|\operatorname{norm}\left(x\right)\right|
$$
