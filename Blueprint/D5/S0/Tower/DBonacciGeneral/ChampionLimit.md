# Champion Limit

## Abstract

The champion value tends to one third, and the slack that powers the finite-depth witness equals the Perron deficit divided by the base less one.

Two facts about the same quantity. The champion value is continuous at the limiting base, so it inherits the known convergence of the Perron root to two. The gap between the predecessor coordinate and that value has a closed form in which positivity below base two is immediate.

**Theorem 1.1 (The slack in closed form).**

$$\forall beta \in R,\; \left(1 < \mathit{beta} \land \mathit{beta} < 2\right) \Rightarrow \operatorname{championMidCoordinate}\left(\mathit{beta}\right) - \operatorname{championValue}\left(\mathit{beta}\right) = \frac{2 - \mathit{beta}}{\mathit{beta} - 1}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionLimit.champion_slack_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Written this way the numerator is the deficit below two and the denominator is positive, so the sign question reduces to the Perron bound with no further algebra.

**Theorem 1.2 (The champion value tends to one third).**

$$\operatorname{Tendsto}\left(\operatorname{championValue}\left(\operatorname{dbonacciPerronRoot}\left(d\right)\right), \mathit{atTop}, \operatorname{nhds}\left(\frac{1}{3}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionLimit.championValue_tendsto_one_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity at the limiting base composed with convergence of the Perron root. The value at base two is one third by direct evaluation.

**Theorem 1.3 (Positive at every order, vanishing in the limit).**

$$\left(\forall d \in N,\; 2 \le d \Rightarrow 0 < \operatorname{championMidCoordinate}\left(\operatorname{dbonacciPerronRoot}\left(d\right)\right) - \operatorname{championValue}\left(\operatorname{dbonacciPerronRoot}\left(d\right)\right)\right) \land \operatorname{Tendsto}\left(\operatorname{championMidCoordinate}\left(\operatorname{dbonacciPerronRoot}\left(d\right)\right) - \operatorname{championValue}\left(\operatorname{dbonacciPerronRoot}\left(d\right)\right), \mathit{atTop}, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionLimit.champion_slack_pos_and_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both halves matter. Positivity at each order is what lets a witness exist at every finite depth; the limit is what stops any single witness from working uniformly in the order.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionLimit.championValue_tendsto_one_third`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionLimit.champion_slack_eq`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionLimit.champion_slack_pos_and_tendsto_zero`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](../DBonacci/PerronRoot.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](ChampionValue.md)
