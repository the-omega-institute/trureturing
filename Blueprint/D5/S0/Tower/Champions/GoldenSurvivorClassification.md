# Golden Survivor Classification

## Abstract

The four strict survivor tubes have the claimed limit, while two stronger source conclusions are false.

The exact finite-depth tubes shrink componentwise to the tail state and the three-state champion cycle. Closing each fixed tube before intersecting over all depths preserves exactly those four component endpoints.

**Theorem 1.1 (The componentwise closed tube limit is four points).**

$$\mathit{goldenBackwardLimitCore} = \mathit{goldenFourPointSet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_backward_limit_core_eq_four_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four tube radii are bounded by powers of phi inverse. Any point on the same side of a limiting endpoint is excluded at a sufficiently deep level, while each endpoint belongs to every componentwise closed tube.

**Theorem 1.2 (No state survives the strict threshold forever).**

$$\forall s \in \mathit{GoldenSurvivorState},\; \neg \left(\forall n \in N,\; s \in \operatorname{goldenBackwardSurvivor}\left(\mathit{goldenStrictSurvivorSet}, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_no_strict_permanent_survivor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Permanent strict survival would put a state in every componentwise closed tube and hence among the four endpoints. The depth-two open tube formula excludes each of those endpoints, giving the required classification-to-survival argument rather than an unsupported jump.

**Theorem 1.3 (Closed permanent survival is not four points).**

$$\exists s \in \mathit{GoldenSurvivorState},\; \left(\forall n \in N,\; s \in \operatorname{goldenBackwardSurvivor}\left(\mathit{goldenClosedSurvivorSet}, n\right)\right) \land \left(\neg s \in \mathit{goldenFourPointSet}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_closed_permanent_not_four_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closing the threshold set before backward iteration is different from closing each of the four nondegenerate strict components. An explicit higher preimage remains in the closed threshold set along its entire preperiodic orbit but is not one of the four listed states. Thus the source's closed-permanent four-point claim is false.

**Theorem 1.4 (The terminal point liminf is the golden inverse).**

$$\operatorname{liminf}\left(\operatorname{goldenSurvivorSequence}\left(1\right), \mathit{atTop}\right) = \mathit{goldenInverse}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_survivor_one_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the frozen real-line survivor, x equal to one is outside the indexed name grid but its distance to the grid is the completed terminal gap. Exact Zeckendorf endpoint calculations give survivor values one at even levels and phi inverse at odd levels, so the liminf is phi inverse.

**Theorem 1.5 (The unrestricted global liminf bound is false).**

$$\neg \left(\forall x \in R,\; \operatorname{liminf}\left(\operatorname{goldenSurvivorSequence}\left(x\right), \mathit{atTop}\right) \le \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_global_liminf_upper_bound_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal-point liminf phi inverse is strictly larger than phi inverse squared over two. Therefore the requested statement for all real x, and consequently its stated real-line supremum equality, cannot be proved from the frozen definition because it is false.

## References

- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_backward_limit_core_eq_four_points`
- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_closed_permanent_not_four_points`
- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_global_liminf_upper_bound_false`
- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_no_strict_permanent_survivor`
- Truth anchor: `D5/S0/Tower/Champions/GoldenSurvivorClassification.golden_survivor_one_liminf`
- Dependency: [D5/S0/Tower/Champions/GoldenSurvivorTubes](GoldenSurvivorTubes.md)
