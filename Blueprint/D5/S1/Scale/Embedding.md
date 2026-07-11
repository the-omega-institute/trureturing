# Golden Real Embedding

`D5/S1/Scale/Embedding` sends the golden integer $a + b \varphi$ to the real number with the same coordinate formula.

## Proposition: Coordinate formula

Lean declaration: `D5/S1/Scale/Embedding.embedding_apply`

$$
\operatorname{embedding}\left(a + b \varphi\right) = a + b \varphi
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

Lean declaration: `D5/S1/Scale/Embedding.embedding_injective`

A coordinate collision with $b \ne 0$ would force the forbidden rational identity

$$
\varphi = \frac{-a}{b}
$$

## Norm recovery

### Theorem: Embedding times conjugate

Lean declaration: `D5/S1/Scale/Embedding.embedding_mul_conj`

$$
\operatorname{embedding}\left(x\right) \operatorname{embedding}\left(\operatorname{conj}\left(x\right)\right) = \operatorname{norm}\left(x\right)
$$

### Theorem: Absolute norm relation

Lean declaration: `D5/S1/Scale/Embedding.abs_embedding_mul_abs_conj`

Taking absolute values gives the corresponding multiplicative relation.

$$
\left|\operatorname{embedding}\left(x\right)\right| \left|\operatorname{embedding}\left(\operatorname{conj}\left(x\right)\right)\right| = \left|\operatorname{norm}\left(x\right)\right|
$$
