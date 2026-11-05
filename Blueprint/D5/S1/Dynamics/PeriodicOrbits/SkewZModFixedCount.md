# Fixed points and zero holonomy in a cyclic skew product

## Abstract

Fixed points of a finite cyclic skew product are exactly zero-holonomy base returns, with one factor for every fiber phase.

**Theorem 1.1 (Fixed-point counting through the holonomy kernel).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/SkewZModFixedCount.fixed_count_skew_zmod`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewZModFixedCount.fixed_count_skew_zmod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an additive skew map with fiber ZMod q, an n-step fixed point must first have an n-step fixed base point. Its fiber coordinate then returns exactly when the n-step Birkhoff sum is zero in ZMod q.

When the holonomy vanishes, every one of the q fiber phases returns; when it does not, no phase returns. The fixed-point count is therefore q times the cardinality of the zero-holonomy return set. This is the counting bridge from the skew group action to the Möbius/Dold layer.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewZModFixedCount.fixed_count_skew_zmod`
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/OrbitCounting](OrbitCounting.md)
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn](SkewAdditiveReturn.md)
