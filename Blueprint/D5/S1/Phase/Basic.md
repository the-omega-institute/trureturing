# Golden Phase

`D5/S1/Phase/Basic` maps an integer $n$ to $n \cdot \varphi \bmod 1$ in the additive circle. The map preserves zero, addition, and negation.

$$
\operatorname{goldenPhase}\left(n\right) = n \cdot \varphi \bmod 1
$$

## Additive laws

### Proposition: Zero

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_zero` `✓ std3`

$$
\operatorname{goldenPhase}\left(0\right) = 0
$$

### Proposition: Addition

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_add` `✓ std3`

$$
\operatorname{goldenPhase}\left(n + m\right) = \operatorname{goldenPhase}\left(n\right) + \operatorname{goldenPhase}\left(m\right)
$$

### Proposition: Negation

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_neg` `✓ std3`

$$
\operatorname{goldenPhase}\left(-n\right) = -\operatorname{goldenPhase}\left(n\right)
$$

## Orbit notation

The same orbit has sequence and set presentations:

$$
p_{n} = n \cdot \varphi \bmod 1
$$

$$
\left(n \cdot \varphi \bmod 1\right)_{n \in \mathbb{Z}}
$$

$$
\left\{n \cdot \varphi \bmod 1 \mid n \in \mathbb{Z}\right\}
$$

## Theorem: Injectivity

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_injective` `✓ std3`

Two phases could coincide only if a nonzero integer multiple of $\varphi$ were an integer. Irrationality excludes this. No three-distance theorem is asserted here.
