# CircleFinitePositiveExpansiveness

## Abstract

Uniform finite positive expansivity implies positive expansivity for every continuous circle selfmap.

**Theorem 1.1 (Local injectivity is derived).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.isLocallyInjective_of_finitelyPositiveExpansive`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.isLocallyInjective_of_finitelyPositiveExpansive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a continuous selfmap of the entire AddCircle (1 : Real), FinitelyPositiveExpansive implies local injectivity. If local injectivity failed, two distinct lifted turns and the proved two-target crossing would extend every actual coalescing history family. Exact transit and fold pullbacks control every time through T+q+1, including the final application of f, and double the family. The resulting 2^N distinct common-terminal histories contradict the original strict infinite-time Bowen bound. Local injectivity is a conclusion of this argument.

**Theorem 1.2 (The exact circle theorem).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every f : AddCircle (1 : Real) -> AddCircle (1 : Real), continuity and FinitelyPositiveExpansive f imply PositivelyExpansive f. The finite hypothesis chooses one epsilon > 0 and one natural N >= 1 uniformly over all centers, bounding the strict forward Bowen set at every natural time including zero. The conclusion supplies its own uniform positive scale c: if dist(f^t(x), f^t(y)) < c for every natural t then x=y. No invertibility, surjectivity, covering, local injectivity, orientation, mixing or expansion hypothesis is imposed. After deriving local injectivity, compactness supplies a uniform injectivity radius. Uniform continuity and the exact short-arc image lemma propagate an endpoint-close short arc at every iterate. If the endpoints differed the entire infinite arc would lie in one original Bowen set, contradicting its finite cardinal bound.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.isLocallyInjective_of_finitelyPositiveExpansive`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive`
- Dependency: [D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder](CircleFinitePositiveExpansiveness/CircleOrder.md)
