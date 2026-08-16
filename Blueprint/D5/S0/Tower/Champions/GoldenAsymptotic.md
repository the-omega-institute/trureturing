# Golden Asymptotic Champion

## Abstract

The golden champion follows a three-phase gap orbit with exact liminf arm.

**Theorem 1.1 (The two exact champion values agree).**

$$\frac{2 - \mathit{phi}}{2} = \frac{\mathit{phi}^{0 - 2}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenAsymptotic.golden_asymptotic_value_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic golden-ratio identity proves directly that (2-phi)/2 equals phi inverse squared divided by two.

**Theorem 1.2 (The containing gap has period three).**

$$\forall k \in N,\; \operatorname{IsGoldenOrbitGap}\left(3 \cdot k + 6, \frac{13}{2} - 4 \cdot \mathit{phi}, \frac{1}{2}, \frac{1}{2}\right) \land \left(\operatorname{IsGoldenOrbitGap}\left(3 \cdot k + 7, \frac{13}{2} - 4 \cdot \mathit{phi}, \frac{\mathit{phi}}{2}, \frac{\mathit{phi}^{0 - 2}}{2}\right) \land \operatorname{IsGoldenOrbitGap}\left(3 \cdot k + 8, \frac{13}{2} - 4 \cdot \mathit{phi}, \frac{\mathit{phi}^{0 - 1}}{2}, \frac{\mathit{phi}^{0 - 1}}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenAsymptotic.golden_champion_gap_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting at level six, refinement follows a large midpoint, a large gap at coordinate phi/2, and a small midpoint. The frozen golden substitution sends these states cyclically as L, L, S.

**Theorem 1.3 (The three exact arm phases).**

$$\forall k \in N,\; \operatorname{goldenSurvivor}\left(3 \cdot k + 6, \frac{13}{2} - 4 \cdot \mathit{phi}\right) = \frac{1}{2} \land \left(\operatorname{goldenSurvivor}\left(3 \cdot k + 7, \frac{13}{2} - 4 \cdot \mathit{phi}\right) = \frac{\mathit{phi}^{0 - 2}}{2} \land \operatorname{goldenSurvivor}\left(3 \cdot k + 8, \frac{13}{2} - 4 \cdot \mathit{phi}\right) = \frac{\mathit{phi}^{0 - 1}}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenAsymptotic.golden_champion_arm_ring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The phase-a declaration gives the level 3k+6 value one half. Its companion phase-b and phase-c theorems give respectively phi inverse squared over two and phi inverse over two.

The separate level-five theorem verifies the single-step in-hull preimage and also has arm phi inverse over two.

**Theorem 1.4 (The champion liminf arm).**

$$\operatorname{liminfAtTop}\left(\operatorname{goldenSurvivor}\left(Q, \frac{13}{2} - 4 \cdot \mathit{phi}\right)\right) = \frac{\mathit{phi}^{0 - 2}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenAsymptotic.golden_champion_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All tail phases are at least phi inverse squared over two, and the phase-b levels occur cofinally, so the along-level filter liminf is exactly that value.

This is not the fixed-level supremum one half. The stronger global supremum over points of their liminf arms remains open here because the available maximizer results classify one level at a time, not the full backward survivor set.

## References

- Truth anchor: `D5/S0/Tower/Champions/GoldenAsymptotic.golden_asymptotic_value_identity`
- Truth anchor: `D5/S0/Tower/Champions/GoldenAsymptotic.golden_champion_arm_ring`
- Truth anchor: `D5/S0/Tower/Champions/GoldenAsymptotic.golden_champion_gap_orbit`
- Truth anchor: `D5/S0/Tower/Champions/GoldenAsymptotic.golden_champion_liminf`
- Dependency: [D5/S0/Tower/GoldenSubstitution](../GoldenSubstitution.md)
- Dependency: [D5/S0/Tower/MetricGeometry/GoldenSurvivor](../MetricGeometry/GoldenSurvivor.md)
