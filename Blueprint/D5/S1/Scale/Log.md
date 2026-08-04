# Golden Logarithmic Scale

## Abstract

Nonzero golden integers have an integer logarithmic scale with exact unit shifts.

`D5/S1/Scale/Log` assigns a scale only when $x \ne 0$. Zero is represented by `none`, never by a fabricated integer.

**Proposition 1.1 (Zero has no scale).**

$\operatorname{logScale}(0)=\operatorname{none}$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Log.logScale_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The option-valued definition returns `none` at zero.

**Proposition 1.2 (Nonzero scale).**

$\forall x \in \operatorname{GoldenInt},\ x\neq 0 \Rightarrow \operatorname{logScale}(x)=\operatorname{some}(\lfloor\log_{\varphi}\lvert\operatorname{embedding}(x)\rvert\rfloor)$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Log.logScale_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero input the following integer is wrapped in `some`:

$$
\operatorname{logScale}\left(x\right) = \operatorname{some}\left(\left\lfloor\log_{\varphi}\left(\left|\operatorname{embedding}\left(x\right)\right|\right)\right\rfloor\right)
$$

## Integral unit shifts

**Proposition 1.3 (Embedding of a unit power).**

$\forall n \in \mathbb{Z},\ \forall x \in \operatorname{GoldenInt},\ \operatorname{embedding}(\operatorname{phiUnitZPowMul}(n,x))=\varphi^{n}\operatorname{embedding}(x)$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Log.embedding_phiUnitZPowMul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

$$
\operatorname{embedding}\left(\operatorname{phiUnitZPowMul}\left(n, x\right)\right) = \varphi^{n} \cdot \operatorname{embedding}\left(x\right)
$$

**Theorem 1.4 (Exact scale translation).**

$\forall n \in \mathbb{Z},\ \forall x \in \operatorname{GoldenInt},\ x\neq 0 \Rightarrow \operatorname{logScale}(\operatorname{phiUnitZPowMul}(n,x))=\operatorname{map}(n+\cdot,\operatorname{logScale}(x))$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Log.logScale_phiUnit_zpow_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the option level, every integer exponent, including negative powers, translates the scale through `map` exactly:

$$
\operatorname{logScale}\left(\operatorname{phiUnitZPowMul}\left(n, x\right)\right) = \operatorname{map}\left(n + \mathord{\cdot}, \operatorname{logScale}\left(x\right)\right)
$$
