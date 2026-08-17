# Strict Finite Depth

## Abstract

Every finite strict Tribonacci backward-survivor depth is nonempty, so the strict forbidden region never becomes empty at a finite depth.

The threshold period-two orbit sits exactly on the strict boundary: its large phase has arm exactly equal to the threshold. Perturbing the large coordinate downward by a budget that the expanding map has not yet inflated past the middle slack keeps every visited arm strictly above the threshold. Choosing the perturbation proportional to a negative power of the Tribonacci constant therefore realizes any prescribed finite depth.

**Theorem 1.1 (Every finite strict depth is nonempty).**

$$\forall n \in N,\; \exists s \in \mathit{TribonacciPeriodicState},\; s \in \operatorname{tribonacciBackwardSurvivor}\left(\mathit{tribonacciStrictSurvivorSet}, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth.tribonacci_strict_backward_survivor_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness is the large champion coordinate reduced by half the middle slack divided by the depth-th power of the Tribonacci constant. The bound is strict at every visited state, so the membership is not a boundary artifact.

**Theorem 1.2 (Depth sixty is nonempty).**

$$\exists s \in \mathit{TribonacciPeriodicState},\; s \in \operatorname{tribonacciBackwardSurvivor}\left(\mathit{tribonacciStrictSurvivorSet}, 60\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth.tribonacci_strict_backward_survivor_sixty_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the direct refutation of the announced emptiness at depth sixty. Interval iteration in one hundred forty decimal digits independently measures the depth-sixty level at about nine times ten to the minus seventeen, and the level is still positive at depth one hundred twenty.

**Theorem 1.3 (Finite depths and the permanent set separate).**

$$\left(\forall n \in N,\; \exists s \in \mathit{TribonacciPeriodicState},\; s \in \operatorname{tribonacciBackwardSurvivor}\left(\mathit{tribonacciStrictSurvivorSet}, n\right)\right) \land \mathit{tribonacciStrictPermanentSet} = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth.tribonacci_finite_depths_nonempty_and_permanent_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The levels are open sets, so a nested intersection may be empty while every level is nonempty. Emptiness of the all-depth intersection therefore decides no finite level, and the two statements are consistent.

## References

- Truth anchor: `D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth.tribonacci_finite_depths_nonempty_and_permanent_empty`
- Truth anchor: `D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth.tribonacci_strict_backward_survivor_nonempty`
- Truth anchor: `D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth.tribonacci_strict_backward_survivor_sixty_nonempty`
- Dependency: [D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors](TribonacciPermanentSurvivors.md)
