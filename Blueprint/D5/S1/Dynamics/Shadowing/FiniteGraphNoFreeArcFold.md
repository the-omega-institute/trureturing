# Local injectivity in the open edges of finite graphs

## Abstract

Local injectivity in the open edges of finite graphs

**Theorem 1.1 (Every positive iterate is locally injective along each open edge).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold.isLocallyInjective_iterate_at_openEdge`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold.isLocallyInjective_iterate_at_openEdge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A collision of an iterate inside a sufficiently short free arc yields a strict local fold after isolating its finite fiber. Strong transitivity pulls the fold into any open subarc. The two disjoint lifts of a common shorter arc then double a close coalescing family. Arbitrary repetition would violate the uniform cardinal bound on forward Bowen balls.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphNoFreeArcFold.isLocallyInjective_iterate_at_openEdge`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization](FiniteGraphAffineRealization.md)
