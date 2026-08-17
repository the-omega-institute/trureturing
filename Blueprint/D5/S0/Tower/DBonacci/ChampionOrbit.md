# Four-Bonacci Champion Orbit

## Abstract

A closed four-bonacci period-two point has a liminf that refutes the initial formula.

**Definition 1.1 (Closed four-bonacci period-two point).**

$$\mathit{x4} = \frac{\mathit{b4}^{0 - 3}}{\mathit{b4}^{2} - 1}$$

*Formalization.* `D5/S0/Tower/DBonacci/ChampionOrbit.dbonacciFourChampionPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With b4 the frozen order-four Perron root, the selected point is b4 inverse-cubed divided by b4 squared minus one. Direct high-precision grid enumeration first located this point before the closed orbit was proved.

**Theorem 1.2 (The containing gap has label-three label-two period two).**

$$\forall k \in N,\; \operatorname{IsDBonacciOrbitGap}\left(4, 2 \cdot k + 4, \mathit{x4}, 3, \frac{\mathit{b4}}{\mathit{b4}^{2} - 1}, \frac{\mathit{b4}^{2} - \mathit{b4} - 1}{\mathit{b4}^{2} - 1}\right) \land \operatorname{IsDBonacciOrbitGap}\left(4, 2 \cdot k + 5, \mathit{x4}, 2, \frac{1}{\mathit{b4}^{2} - 1}, \mathit{b4} \cdot \frac{\mathit{b4}^{2} - \mathit{b4} - 1}{\mathit{b4}^{2} - 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/ChampionOrbit.four_champion_gap_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At levels 2k+4 the point lies in a largest label-three gap, with normalized arms b4/(b4 squared minus one) and the corrected low arm. The right refinement enters label two; the following left refinement returns to label three. The proof uses the local substitution law and therefore retains its boundary terms.

**Theorem 1.3 (Exact survivor values on both phases).**

$$\forall k \in N,\; \operatorname{dbonacciSurvivor}\left(4, 2 \cdot k + 4, \mathit{x4}\right) = \frac{\mathit{b4}^{2} - \mathit{b4} - 1}{\mathit{b4}^{2} - 1}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/ChampionOrbit.four_champion_survivor_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized distance at every level 2k+4 is exactly (b4 squared minus b4 minus one)/(b4 squared minus one).

The companion odd-level theorem gives 1/(b4 squared minus one) at every level 2k+5.

$$
\forall k \in N,\; \operatorname{dbonacciSurvivor}\left(4, 2 \cdot k + 5, \mathit{x4}\right) = \frac{1}{\mathit{b4}^{2} - 1}
$$

**Theorem 1.4 (Exact liminf of the four-bonacci orbit).**

$$\operatorname{liminfAtTop}\left(\operatorname{dbonacciSurvivor}\left(4, Q, \mathit{x4}\right)\right) = \frac{\mathit{b4}^{2} - \mathit{b4} - 1}{\mathit{b4}^{2} - 1}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/ChampionOrbit.dbonacci_four_champion_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The low phase occurs cofinally and every eventual value is at least that phase, so the along-level filter liminf is the corrected low arm.

This theorem concerns one fixed point as Q tends to infinity. A fixed-Q upper bound, or a supremum over all points, is a different quantity; neither is substituted for this liminf, and no global championship claim is made here.

**Theorem 1.5 (The initial candidate is strictly too small at order four).**

$$\frac{1 - \mathit{b4}^{0 - 1}}{2} < \operatorname{liminfAtTop}\left(\operatorname{dbonacciSurvivor}\left(4, Q, \mathit{x4}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/ChampionOrbit.dbonacci_four_initial_candidate_lt_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Thus (1-b4 inverse)/2 is not the four-bonacci value. The companion inequality theorem records explicit disequality. Agreement at orders two and three therefore does not establish a formula for all d.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/ChampionOrbit.dbonacciFourChampionPoint`
- Truth anchor: `D5/S0/Tower/DBonacci/ChampionOrbit.dbonacci_four_champion_liminf`
- Truth anchor: `D5/S0/Tower/DBonacci/ChampionOrbit.dbonacci_four_initial_candidate_lt_liminf`
- Truth anchor: `D5/S0/Tower/DBonacci/ChampionOrbit.four_champion_gap_orbit`
- Truth anchor: `D5/S0/Tower/DBonacci/ChampionOrbit.four_champion_survivor_even`
- Dependency: [D5/S0/Tower/DBonacci/Substitution](Substitution.md)
- Dependency: [D5/S0/Tower/DBonacci/Survivor](Survivor.md)
