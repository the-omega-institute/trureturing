# General D-Bonacci ba Champion

## Abstract

The universal ba fixed point closes the corrected d-bonacci champion liminf.

**Definition 1.1 (Universal ba fixed point).**

$$\operatorname{baFixedPoint}\left(\mathit{beta}\right) = \frac{\mathit{beta}}{\mathit{beta}^{2} - 1}$$

*Formalization.* `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.baFixedPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized large arm fixed by the right-left ba return is beta over beta squared minus one.

**Theorem 1.2 (The ba return fixes the displayed arm).**

$$\forall beta \in R,\; 1 < \mathit{beta} \Rightarrow \operatorname{baReturn}\left(\mathit{beta}, \operatorname{baFixedPoint}\left(\mathit{beta}\right)\right) = \operatorname{baFixedPoint}\left(\mathit{beta}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.ba_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real beta above one, the affine map beta times (beta u minus one) returns beta over beta squared minus one.

**Theorem 1.3 (The corrected value is the complementary arm).**

$$\forall beta \in R,\; 1 < \mathit{beta} \Rightarrow \operatorname{championValue}\left(\mathit{beta}\right) = 1 - \operatorname{baFixedPoint}\left(\mathit{beta}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.championValue_eq_one_sub_baFixedPoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The low arm is one minus the universal ba fixed point, yielding the rational champion expression.

**Theorem 1.4 (Every order has the same typed ba orbit).**

$$\forall d \in N,\; 3 \le d \Rightarrow \left(\forall k \in N,\; \operatorname{dbonacciChampionGapOrbit}\left(d, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.dbonacci_champion_gap_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal top-gap witness and the typed substitution algebra produce the two alternating survivor arms at levels 2k+d and 2k+d+1.

**Theorem 1.5 (The universal corrected liminf).**

$$\forall d \in N,\; 3 \le d \Rightarrow \operatorname{liminfAtTop}\left(\operatorname{dbonacciSurvivor}\left(d, Q, \operatorname{dbonacciChampionPoint}\left(d\right)\right)\right) = \operatorname{championValue}\left(\operatorname{dbonacciPerronRoot}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.dbonacci_champion_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least three, the exact liminf along the ba point is championValue of the d-bonacci Perron root.

**Theorem 1.6 (Order four is a general-theorem instance).**

$$\operatorname{liminfAtTop}\left(\operatorname{dbonacciSurvivor}\left(4, Q, \operatorname{dbonacciFourChampionPoint}\left(\right)\right)\right) = \frac{\mathit{b4}^{2} - \mathit{b4} - 1}{\mathit{b4}^{2} - 1}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.four_champion_liminf_from_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corrected order-four liminf is obtained from the all-order theorem after identifying its closed point with the existing hand instance.

## References

- Truth anchor: `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.baFixedPoint`
- Truth anchor: `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.ba_fixed_point`
- Truth anchor: `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.championValue_eq_one_sub_baFixedPoint`
- Truth anchor: `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.dbonacci_champion_gap_orbit`
- Truth anchor: `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.dbonacci_champion_liminf`
- Truth anchor: `D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.four_champion_liminf_from_general`
- Dependency: [D5/S0/Tower/DBonacci/ChampionOrbit](../DBonacci/ChampionOrbit.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](../DBonacciGeneral/ChampionValue.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/UniformBaseGap](../DBonacciGeneral/UniformBaseGap.md)
