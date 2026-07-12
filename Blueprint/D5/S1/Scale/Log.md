# Golden Logarithmic Scale

`D5/S1/Scale/Log` assigns a scale only when $x \ne 0$. Zero is represented by `none`, never by a fabricated integer.

## Proposition: Zero has no scale

Lean declaration: `D5/S1/Scale/Log.logScale_zero` `✓ std3`

The option-valued definition returns `none` at zero.

## Proposition: Nonzero scale

Lean declaration: `D5/S1/Scale/Log.logScale_ne_zero` `✓ std3`

For nonzero input the following integer is wrapped in `some`:

$$
\operatorname{logScale}\left(x\right) = \operatorname{some}\left(\left\lfloor\log_{\varphi}\left(\left|\operatorname{embedding}\left(x\right)\right|\right)\right\rfloor\right)
$$

## Integral unit shifts

### Proposition: Embedding of a unit power

Lean declaration: `D5/S1/Scale/Log.embedding_phiUnitZPowMul` `✓ std3`

$$
\operatorname{embedding}\left(\operatorname{phiUnitZPowMul}\left(n, x\right)\right) = \varphi^{n} \operatorname{embedding}\left(x\right)
$$

### Theorem: Exact scale translation

Lean declaration: `D5/S1/Scale/Log.logScale_phiUnit_zpow_mul` `✓ std3`

At the option level, every integer exponent, including negative powers, translates the scale through `map` exactly:

$$
\operatorname{logScale}\left(\operatorname{phiUnitZPowMul}\left(n, x\right)\right) = \operatorname{map}\left(n + \mathord{\cdot}, \operatorname{logScale}\left(x\right)\right)
$$
