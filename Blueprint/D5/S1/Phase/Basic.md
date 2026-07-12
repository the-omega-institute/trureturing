# Golden Phase

`D5/S1/Phase/Basic` maps an integer $n$ to $n \varphi \bmod 1$ in the additive circle. The map preserves zero, addition, and negation.

$$
\operatorname{goldenPhase}\left(n\right) = n \varphi \bmod 1
$$

## Additive laws

### Proposition: Zero

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_zero` `✓ std3`

$$
\operatorname{goldenPhase}\left(0\right) = 0
$$

### Proposition: Addition

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_add` `✓ std3`

$$
\operatorname{goldenPhase}\left(n + m\right) = \operatorname{goldenPhase}\left(n\right) + \operatorname{goldenPhase}\left(m\right)
$$

### Proposition: Negation

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_neg` `✓ std3`

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

Lean declaration: `D5/S1/Phase/Basic.goldenPhase_injective` `✓ std3`

Compiled Lean statement: `D5/S1/Phase/Basic.goldenPhase_injective` `✓ std3`

```text
statement-v1(uparams=[],type=ea(ea(ea(ec(ns(ns(n0,8:Function),9:Injective),[ls(l0),ls(l0)]),ec(ns(n0,3:Int),[])),ea(ea(ea(ec(ns(n0,9:AddCircle),[l0]),ec(ns(n0,4:Real),[])),ec(ns(ns(n0,4:Real),16:instAddCommGroup),[])),ea(ea(ea(ec(ns(ns(n0,5:OfNat),5:ofNat),[l0]),ec(ns(n0,4:Real),[])),ei(ln(1))),ea(ea(ec(ns(ns(n0,3:One),8:toOfNat1),[l0]),ec(ns(n0,4:Real),[])),ec(ns(ns(n0,4:Real),7:instOne),[]))))),ec(ns(ns(ns(ns(n0,2:D5),2:S1),5:Phase),11:goldenPhase),[])))
```

Two phases could coincide only if a nonzero integer multiple of $\varphi$ were an integer. Irrationality excludes this. No three-distance theorem is asserted here.
