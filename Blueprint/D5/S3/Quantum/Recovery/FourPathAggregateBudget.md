# Four-path aggregate stability budgets

## Abstract

Finite certificate families carry a uniform quadratic ray-distance budget, a compatible quartic budget, and the numerical square-root budget used by the padded Kraus comparison.

**Theorem 1.1 (Certificate distance budget).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathAggregateBudget.certificate_distance_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathAggregateBudget.certificate_distance_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pointwise certificate gap bounded by 1600 times the coordinatewise minimum sums to the same bound for the finite family.

**Theorem 1.2 (Quartic distance budget).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathAggregateBudget.quartic_distance_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathAggregateBudget.quartic_distance_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under complete coordinate totals, every minimum lies in the unit interval, so its square inherits the quadratic certificate budget.

**Theorem 1.3 (Square-root budget).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathAggregateBudget.square_root_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathAggregateBudget.square_root_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The column estimate, certificate budget, and actual trace-defect identity propagate to the constant 480 times square root of 2 times square root of epsilon.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathAggregateBudget.certificate_distance_budget`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathAggregateBudget.quartic_distance_budget`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathAggregateBudget.square_root_budget`
- Dependency: [D5/S3/Quantum/Recovery/FourPathNearestRayComparison](FourPathNearestRayComparison.md)
- Dependency: [D5/S3/Quantum/Recovery/FourPathQuadraticMajorant](FourPathQuadraticMajorant.md)
