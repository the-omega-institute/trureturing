# Golden Finite Depth

## Abstract

Every finite strict golden backward-survivor depth is nonempty, so the strict forbidden region never becomes empty at a finite depth.

The boundary champion orbit has period three and passes through a large state whose arm is exactly the threshold. Perturbing that coordinate downward by a budget the expanding map has not yet inflated past the tightest phase constraint keeps every visited arm strictly above the threshold. Choosing the perturbation proportional to a negative power of the golden ratio therefore realizes any prescribed finite depth.

**Theorem 1.1 (Every finite strict depth is nonempty).**

$$\forall n \in N,\; \exists s \in \mathit{GoldenSurvivorState},\; s \in \operatorname{goldenBackwardSurvivor}\left(\mathit{goldenStrictSurvivorSet}, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenStrictDepth/FiniteDepth.golden_strict_backward_survivor_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness is the large boundary coordinate reduced by half the budget divided by the depth-th power of the golden ratio. The bound is strict at every visited state, so the membership is not a boundary artifact.

**Theorem 1.2 (Depth sixty is nonempty).**

$$\exists s \in \mathit{GoldenSurvivorState},\; s \in \operatorname{goldenBackwardSurvivor}\left(\mathit{goldenStrictSurvivorSet}, 60\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenStrictDepth/FiniteDepth.golden_strict_backward_survivor_sixty_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interval iteration in one hundred forty decimal digits independently measures the depth-sixty level at about two times ten to the minus thirteen, and the level is still positive at depth one hundred.

**Theorem 1.3 (Finite depths and the permanent set separate).**

$$\left(\forall n \in N,\; \exists s \in \mathit{GoldenSurvivorState},\; s \in \operatorname{goldenBackwardSurvivor}\left(\mathit{goldenStrictSurvivorSet}, n\right)\right) \land \mathit{goldenStrictPermanentSet} = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenStrictDepth/FiniteDepth.golden_finite_depths_nonempty_and_permanent_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The levels are open sets, so a nested intersection may be empty while every level is nonempty. Emptiness of the all-depth intersection therefore decides no finite level, and the two statements are consistent.

## References

- Truth anchor: `D5/S0/Tower/GoldenStrictDepth/FiniteDepth.golden_finite_depths_nonempty_and_permanent_empty`
- Truth anchor: `D5/S0/Tower/GoldenStrictDepth/FiniteDepth.golden_strict_backward_survivor_nonempty`
- Truth anchor: `D5/S0/Tower/GoldenStrictDepth/FiniteDepth.golden_strict_backward_survivor_sixty_nonempty`
- Dependency: [D5/S0/Tower/Champions/GoldenPermanentSurvivors](../Champions/GoldenPermanentSurvivors.md)
