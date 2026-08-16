# Five-Bonacci Champion Orbit

## Abstract

A closed five-bonacci period-two point attains the corrected champion arm.

**Definition 1.1 (Closed five-bonacci period-two point).**

$$\mathit{x5} = \frac{\mathit{b5}^{0 - 4}}{\mathit{b5}^{2} - 1}$$

*Formalization.* `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacciFiveChampionPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With b5 the order-five Perron root, this is the real point whose tail digits are 1010... beginning at position six.

**Theorem 1.2 (The containing gap has label-four label-three period two).**

$$\forall k \in N,\; \operatorname{IsDBonacciOrbitGap}\left(5, 2 \cdot k + 5, \mathit{x5}, 4, \frac{\mathit{b5}}{\mathit{b5}^{2} - 1}, \frac{\mathit{b5}^{2} - \mathit{b5} - 1}{\mathit{b5}^{2} - 1}\right) \land \operatorname{IsDBonacciOrbitGap}\left(5, 2 \cdot k + 6, \mathit{x5}, 3, \frac{1}{\mathit{b5}^{2} - 1}, \mathit{b5} \cdot \frac{\mathit{b5}^{2} - \mathit{b5} - 1}{\mathit{b5}^{2} - 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.five_champion_gap_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At levels 2k+5 the point lies in a largest label-four gap. Its right refinement enters label three, and the next left refinement returns to label four. The proof reuses the general d-bonacci substitution and survivor carrier supplied by the order-four development.

**Theorem 1.3 (Exact liminf of the five-bonacci orbit).**

$$\operatorname{liminfAtTop}\left(\operatorname{dbonacciSurvivor}\left(5, Q, \mathit{x5}\right)\right) = \operatorname{championValue}\left(\mathit{b5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacci_five_champion_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The even phase is exactly championValue(b5), the odd phase is the larger middle arm, and the low phase occurs cofinally. This proves an attaining orbit; it does not replace the separate all-points upper bound needed for a global extremality theorem.

**Theorem 1.4 (Order-five champion-arm numerical certificate).**

$$\operatorname{abs}\left(\operatorname{liminfAtTop}\left(\operatorname{dbonacciSurvivor}\left(5, Q, \mathit{x5}\right)\right) - \frac{313794}{1000000}\right) < \frac{1}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacci_five_champion_liminf_numeric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact orbit liminf differs from 0.313794 by less than one millionth.

**Theorem 1.5 (The initial expression fails on the five-bonacci orbit).**

$$\frac{1 - \mathit{b5}^{0 - 1}}{2} \ne \operatorname{liminfAtTop}\left(\operatorname{dbonacciSurvivor}\left(5, Q, \mathit{x5}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacci_five_initial_formula_ne_champion_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial expression (1-b5 inverse)/2 is unequal to the exact liminf of this period-two point.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacciFiveChampionPoint`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacci_five_champion_liminf`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacci_five_champion_liminf_numeric`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.dbonacci_five_initial_formula_ne_champion_liminf`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit.five_champion_gap_orbit`
- Dependency: [D5/S0/Tower/DBonacci/ChampionOrbit](../DBonacci/ChampionOrbit.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](ChampionValue.md)
