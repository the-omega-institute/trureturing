# Finite sets missed by iterated arcs in transitive graphs

## Abstract

Finite sets missed by iterated arcs in transitive graphs

**Theorem 1.1 (The forward images of a free subarc miss a finite totally invariant set).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier.exists_edgeChart_Icc_finite_exceptional_set`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier.exists_edgeChart_Icc_finite_exceptional_set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty open set in a nontrivial connected finite graph contains a closed free subarc. Transitivity supplies a positive return time for the arc. Images with indices in the same residue class form a connected union, and the closure of each such union adds only finitely many points. Their dense union therefore has a finite complement, which the map permutes and whose full preimage equals itself.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier.exists_edgeChart_Icc_finite_exceptional_set`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphSmallArcs](FiniteGraphSmallArcs.md)
