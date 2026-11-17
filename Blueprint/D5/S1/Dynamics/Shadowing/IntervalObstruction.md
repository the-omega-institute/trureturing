# IntervalObstruction

## Abstract

Every continuous nondegenerate compact real-interval selfmap fails finite positive expansivity.

**Theorem 1.1 (Arbitrarily many distinct all-time close witnesses).**

Lean statement: `D5/S1/Dynamics/Shadowing/IntervalObstruction.interval_bowen_witnesses`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/IntervalObstruction.interval_bowen_witnesses` (`✓ std3`). ∎

*Citation.* Silvère Gangloff; Pierre Guillon; Piotr Oprocha (2023). *Various questions around finitely positively expansive dynamical systems*. URL: <https://arxiv.org/abs/2310.17241v1>.

*Commentary.*

For every real a < b, every continuous f : Icc a b -> Icc a b, every epsilon > 0 and every natural N, there are a center x and an injective family y : Fin (N+1) -> Icc a b such that dist(f^t(x), f^t(y_i)) < epsilon for every i and every natural t. Neither onto dynamics nor a monotonicity hypothesis is required. This is the arbitrary closed-interval, finite-family formulation of the known interval obstruction in Theorem 3.8 of the cited source; the repository supplies a direct Lean proof. The witnesses are consumed by the circle argument.

**Theorem 1.2 (The interval obstruction).**

Lean statement: `D5/S1/Dynamics/Shadowing/IntervalObstruction.interval_not_finitelyPositiveExpansive`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/IntervalObstruction.interval_not_finitelyPositiveExpansive` (`✓ std3`). ∎

*Citation.* Silvère Gangloff; Pierre Guillon; Piotr Oprocha (2023). *Various questions around finitely positively expansive dynamical systems*. URL: <https://arxiv.org/abs/2310.17241v1>.

*Commentary.*

Every continuous selfmap of the actual nondegenerate compact interval fails FinitelyPositiveExpansive. This is the known interval obstruction in Theorem 3.8 of the cited source, proved directly here for arbitrary real endpoints and used as a supplier in the circle theorem. Overlapping macroscopic iterate images yield an invariant interval if every iterate is injective; orientation gluing, finite fibres and monotone trapping rule that case out. Otherwise exact disjoint fold pullbacks double coalescing histories. Equality at a common terminal time controls the entire infinite tail, while the construction controls every earlier time including zero and the terminal time. The argument produces 2^N distinct histories against the same uniform N. The subtype extension preserves the original dynamics and all-time Bowen condition.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/IntervalObstruction.interval_bowen_witnesses`
- Truth anchor: `D5/S1/Dynamics/Shadowing/IntervalObstruction.interval_not_finitelyPositiveExpansive`
- Dependency: [D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic](IntervalObstruction/Basic.md)
