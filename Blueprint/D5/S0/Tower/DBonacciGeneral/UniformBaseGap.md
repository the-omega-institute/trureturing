# Uniform D-Bonacci Base Gap

## Abstract

The diagonal d-bonacci layer admits one uniform typed top-gap base construction.

The construction replaces order-by-order cardinality calculations and bounded-name recursion with two diagonal facts: the layer has 2^d-1 names, and its first two indexed values are zero and beta_d to the minus d. The point and complementary-arm equations remain explicit scalar hypotheses.

**Theorem 1.1 (Diagonal cardinality has a closed form).**

$$\forall d \in N,\; \operatorname{dbonacci}\left(d, d + 2\right) = 2^{d} - 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.dbonacci_diagonal_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At Q=d the d-bonacci recurrence still sees only its binary initial segment, so the cardinality is the geometric sum 2^d-1.

**Theorem 1.2 (The first diagonal value is zero).**

$$\forall d \in N,\; d \ge 1 \Rightarrow \operatorname{indexedNameValue}\left(d, d, 0\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.diagonal_first_index_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded-run indexing recursion sends index zero through its lower branch at every level and hence evaluates to zero.

**Theorem 1.3 (The second diagonal value is beta to the minus d).**

$$\forall d \in N,\; d \ge 2 \Rightarrow \operatorname{indexedNameValue}\left(d, d, 1\right) = \operatorname{dbonacciPerronRoot}\left(d\right)^{0 - d}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.diagonal_first_index_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniform induction through the bounded-name recursion keeps index one in the lower branch until its unique final occupied digit.

**Theorem 1.4 (Uniform typed top-gap construction).**

$$\forall d \in N, x \in R, L \in R, R \in R,\; \left(d \ge 3 \land \left(x = L \cdot \operatorname{dbonacciPerronRoot}\left(d\right)^{0 - d} \land L + R = 1\right)\right) \Rightarrow \operatorname{IsDBonacciLetterOrbitGap}\left(d, d, x, \operatorname{topGapLetter}\left(d\right), L, R\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.diagonal_top_base_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least three, the gap between indices zero and one is the typed top letter. A point scaled from its left arm by beta_d^{-d}, together with complementary arms, supplies the two endpoint distances.

**Theorem 1.5 (The tribonacci base gap is an instance).**

$$\operatorname{IsDBonacciLetterOrbitGap}\left(3, 3, \mathit{tribonacciChampionPoint}, \operatorname{topGapLetter}\left(3\right), \frac{\mathit{beta3}^{2} - \mathit{beta3}}{2}, \frac{1 - \mathit{beta3}^{0 - 1}}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.tribonacci_champion_base_gap_typed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order-three champion point and its frozen coordinate-sum identity instantiate the uniform construction.

**Theorem 1.6 (The four-bonacci base gap is an instance).**

$$\operatorname{IsDBonacciLetterOrbitGap}\left(4, 4, \mathit{dbonacciFourChampionPoint}, \operatorname{topGapLetter}\left(4\right), \frac{\operatorname{dbonacciPerronRoot}\left(4\right)}{\operatorname{dbonacciPerronRoot}\left(4\right)^{2} - 1}, \frac{\operatorname{dbonacciPerronRoot}\left(4\right)^{2} - \operatorname{dbonacciPerronRoot}\left(4\right) - 1}{\operatorname{dbonacciPerronRoot}\left(4\right)^{2} - 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.four_champion_base_gap_typed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order-four scaled-point and arm-sum identities are the only order-specific inputs.

**Theorem 1.7 (The five-bonacci base gap is an instance).**

$$\operatorname{IsDBonacciLetterOrbitGap}\left(5, 5, \mathit{dbonacciFiveChampionPoint}, \operatorname{topGapLetter}\left(5\right), \frac{\operatorname{dbonacciPerronRoot}\left(5\right)}{\operatorname{dbonacciPerronRoot}\left(5\right)^{2} - 1}, \frac{\operatorname{dbonacciPerronRoot}\left(5\right)^{2} - \operatorname{dbonacciPerronRoot}\left(5\right) - 1}{\operatorname{dbonacciPerronRoot}\left(5\right)^{2} - 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.five_champion_base_gap_typed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order-five scaled-point and arm-sum identities give the third direct specialization of the same theorem.

**Theorem 1.8 (The legacy order-four base gap is recovered).**

$$\operatorname{IsDBonacciOrbitGap}\left(4, 4, \mathit{dbonacciFourChampionPoint}, 3, \frac{\operatorname{dbonacciPerronRoot}\left(4\right)}{\operatorname{dbonacciPerronRoot}\left(4\right)^{2} - 1}, \frac{\operatorname{dbonacciPerronRoot}\left(4\right)^{2} - \operatorname{dbonacciPerronRoot}\left(4\right) - 1}{\operatorname{dbonacciPerronRoot}\left(4\right)^{2} - 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.four_champion_base_gap_reproved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For order four the typed top letter evaluates to legacy label three. This converts the new uniform instance back to the original public statement without invoking its frozen proof.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.dbonacci_diagonal_cardinality`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.diagonal_first_index_one`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.diagonal_first_index_zero`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.diagonal_top_base_gap`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.five_champion_base_gap_typed`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.four_champion_base_gap_reproved`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.four_champion_base_gap_typed`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/UniformBaseGap.tribonacci_champion_base_gap_typed`
- Dependency: [D5/S0/Tower/DBonacci/OrbitAlgebra](../DBonacci/OrbitAlgebra.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit](FiveChampionOrbit.md)
- Dependency: [D5/S0/Tower/Tribonacci/ChampionOrbit](../Tribonacci/ChampionOrbit.md)
