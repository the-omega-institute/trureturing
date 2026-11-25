# Relabeling the marked coordinate

## Abstract

Transfer a single-coordinate budget by permuting the coordinates.

**Theorem 1.1 (Every marked coordinate has the same feasible budgets).**

$$\operatorname{AxisFactorWithin}\left(k, i, b\right) \Leftrightarrow \operatorname{AxisFactorWithin}\left(k, j, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/CoordinateRelabel.axis_feasibility_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any dimension d, take marked coordinates i and j in Fin d, a natural multiplier k and a natural budget b. AxisFactorWithin is the one-coordinate Boolean inclusion factor predicate at that multiplier and budget.

Apply the transposition of i and j to the elements of each row and column subset. Inclusion, subset sizes and the full-set pivot are preserved. Transport each entry along these bijections. Each row and column keeps its degree and the exceptional loop remains absent. The charge is unchanged because it counts edges between the same odd ranks away from the full row.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/CoordinateRelabel.axis_feasibility_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor](../ParitySeedAxisFactor.md)
