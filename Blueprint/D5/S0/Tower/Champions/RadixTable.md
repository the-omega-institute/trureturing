# Radix Champion Table

## Abstract

The constant arm and exact odd/even radix champions form one packaged table.

**Theorem 1.1 (Radix champion table).**

$$\forall b \in N, Q \in N,\; \left(b \ge 2 \land Q \ge 1\right) \Rightarrow \left(b^{Q} \cdot \operatorname{radixDistance}\left(b, Q, \frac{1}{b + 1}\right) = \frac{1}{b + 1} \land \left(\left(\operatorname{Odd}\left(b\right) \Rightarrow \operatorname{sSup}\left(\operatorname{eventualLowerBounds}\left(b\right)\right) = \frac{1}{2}\right) \land \left(\operatorname{Even}\left(b\right) \Rightarrow \left(b^{Q} \cdot \operatorname{radixDistance}\left(b, Q, \frac{\frac{b}{2}}{b + 1}\right) = \frac{b}{2 \cdot \left(b + 1\right)} \land \operatorname{sSup}\left(\operatorname{eventualLowerBounds}\left(b\right)\right) = \frac{b}{2 \cdot \left(b + 1\right)}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/RadixTable.radix_champion_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every radix b at least two and positive level Q, the reciprocal point has its exact constant arm. Odd radices have champion supremum one half, attained in the frozen source theorem by x equal to one half. Even radices have both the exact half-radix constant arm and the matching exact champion supremum.

This declaration is only a conjunction packaging four frozen theorems for single-GID coverage; it contains no new mathematics.

## References

- Truth anchor: `D5/S0/Tower/Champions/RadixTable.radix_champion_table`
- Dependency: [D5/S0/Tower/ChampionExtremality](../ChampionExtremality.md)
- Dependency: [D5/S0/Tower/ConstantArms](../ConstantArms.md)
