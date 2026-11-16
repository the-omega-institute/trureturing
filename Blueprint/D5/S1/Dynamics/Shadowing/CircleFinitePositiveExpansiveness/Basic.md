# CircleFinitePositiveExpansiveness - Basic

## Abstract

Actual quotient-metric circle arcs, exact pullbacks, small crossings and strict turns.

**Theorem 1.1 (Proper compact connected circle sets are arcs).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.arc_of_compact_connected`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.arc_of_compact_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Circle is the entire AddCircle (1 : Real) with its quotient metric. Arc is an actual projected nondegenerate real segment of length less than one. A compact connected infinite proper circle subset is represented by such an arc after cutting at a missing point. Trapping an arc under a positive iterate contradicts the interval obstruction via an actual compact embedding and a uniformly continuous injective semiconjugacy.

**Theorem 1.2 (Two genuine turns from failure of local injectivity).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.two_distinct_lifted_turns`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.two_distinct_lifted_turns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under continuity and the uniform finite all-time bound, failure of local injectivity produces two distinct actual circle points at strict extrema of a continuous real lift. Finite fibres isolate extrema. If no second turn exists, the complementary interval restriction is injective and monotone; the lift translation identity from covering uniqueness contradicts the translated first extremum. No degree, orientation or local injectivity is assumed.

**Theorem 1.3 (Exact transport of a short arc).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.image_shortArc`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.image_shortArc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a continuous circle map is injective on the actual short arc from x to y and its image remains within distance 1/8 of f(x), that image equals the short arc from f(x) to f(y). Quotient coordinates and interval monotonicity prove the equality; this supplies the final all-time arc induction.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.arc_of_compact_connected`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.image_shortArc`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic.two_distinct_lifted_turns`
- Dependency: [D5/S1/Dynamics/Shadowing/IntervalObstruction](../IntervalObstruction.md)
