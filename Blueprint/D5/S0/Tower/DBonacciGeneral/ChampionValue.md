# D-Bonacci Champion Value

## Abstract

The corrected d-bonacci champion expression has exact Tribonacci, golden-ratio, endpoint, and low-order numerical checks.

**Definition 1.1 (Corrected algebraic value).**

$$\operatorname{championValue}\left(\mathit{beta}\right) = \frac{\mathit{beta}^{2} - \mathit{beta} - 1}{\mathit{beta}^{2} - 1}$$

*Formalization.* `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For d-bonacci champion claims this expression is used only for orders d at least three. Its order-two evaluation is recorded separately and is not identified with the degenerate-phase tower value.

**Theorem 1.2 (The two Tribonacci expressions coincide).**

$$\operatorname{championValue}\left(t\right) = \frac{1 - t^{0 - 1}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_tribonacciConstant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Tribonacci cubic reduces the corrected rational expression to the frozen low arm. A companion theorem rewrites the existing period-two liminf directly as championValue(t).

**Theorem 1.3 (The order-two numerator vanishes).**

$$\mathit{phi}^{2} - \mathit{phi} - 1 = 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.goldenRatio_championValue_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is exactly the quadratic equation phi squared equals phi plus one.

**Theorem 1.4 (The corrected expression is zero at phi).**

$$\operatorname{championValue}\left(\mathit{phi}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_goldenRatio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero is the value of this rational expression, not the distinct degenerate-phase champion value.

**Theorem 1.5 (The endpoint weld is one third).**

$$\operatorname{championValue}\left(2\right) = \frac{1}{3}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct substitution at beta equal to two gives the exact value one third.

**Theorem 1.6 (The initial formula coincides exactly on the Tribonacci cubic).**

$$\forall beta \in R,\; 1 < \mathit{beta} \Rightarrow \left(\frac{1 - \mathit{beta}^{0 - 1}}{2} = \operatorname{championValue}\left(\mathit{beta}\right) \Leftrightarrow \mathit{beta}^{3} = \mathit{beta}^{2} + \mathit{beta} + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.initialFormula_eq_championValue_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real beta above one, equality of the initial and corrected expressions is equivalent to the Tribonacci cubic equation.

**Theorem 1.7 (The initial formula fails at order five).**

$$\frac{1 - \mathit{b5}^{0 - 1}}{2} \ne \operatorname{championValue}\left(\mathit{b5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.dbonacci_five_initial_formula_ne_championValue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict growth of the d-bonacci Perron roots excludes the order-five root from the Tribonacci coincidence locus.

**Theorem 1.8 (Order-three numerical certificate).**

$$\operatorname{abs}\left(\operatorname{championValue}\left(\mathit{b3}\right) - \frac{228155}{1000000}\right) < \frac{1}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_three_numeric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact value differs from 0.228155 by less than one millionth.

**Theorem 1.9 (Order-four numerical certificate).**

$$\operatorname{abs}\left(\operatorname{championValue}\left(\mathit{b4}\right) - \frac{290162}{1000000}\right) < \frac{1}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_four_numeric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact value differs from 0.290162 by less than one millionth.

**Theorem 1.10 (Order-five numerical certificate).**

$$\operatorname{abs}\left(\operatorname{championValue}\left(\mathit{b5}\right) - \frac{313794}{1000000}\right) < \frac{1}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_five_numeric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact value differs from 0.313794 by less than one millionth.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_five_numeric`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_four_numeric`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_goldenRatio`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_three_numeric`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_tribonacciConstant`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_two`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.dbonacci_five_initial_formula_ne_championValue`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.goldenRatio_championValue_numerator`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionValue.initialFormula_eq_championValue_iff`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](../DBonacci/PerronRoot.md)
- Dependency: [D5/S0/Tower/Tribonacci/ChampionOrbit](../Tribonacci/ChampionOrbit.md)
