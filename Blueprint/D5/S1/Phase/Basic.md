# Golden Phase

`D5/S1/Phase/Basic` maps an integer $n$ to $n \varphi \bmod 1$ in the additive circle. The map preserves zero, addition, and negation.

$$
\operatorname{goldenPhase}\left(n\right) = n \varphi \bmod 1
$$

## Additive laws

### Proposition: Zero

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_zero`

$$
\operatorname{goldenPhase}\left(0\right) = 0
$$

### Proposition: Addition

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_add`

$$
\operatorname{goldenPhase}\left(n + m\right) = \operatorname{goldenPhase}\left(n\right) + \operatorname{goldenPhase}\left(m\right)
$$

### Proposition: Negation

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_neg`

$$
\operatorname{goldenPhase}\left(-n\right) = -\operatorname{goldenPhase}\left(n\right)
$$

## Orbit notation

The same orbit has sequence and set presentations:

$$
p_{n} = n \varphi \bmod 1
$$

$$
\left(n \varphi \bmod 1\right)_{n \in \mathbb{Z}}
$$

$$
\left\{n \varphi \bmod 1 \mid n \in \mathbb{Z}\right\}
$$

## Theorem: Injectivity

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_injective`

Two phases could coincide only if a nonzero integer multiple of $\varphi$ were an integer. Irrationality excludes this. No three-distance theorem is asserted here.
