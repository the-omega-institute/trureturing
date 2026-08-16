# Bellman Maximum Equation

## Abstract

Discounted prediction distance satisfies its one-step Bellman maximum equation.

**Theorem 1.1 (Discounted prediction distance obeys the Bellman maximum equation).**

$$\forall \gamma\in(0, 1], \forall a, b\in O,\ 0\leq d_{O}(a, b)\leq D \Rightarrow \forall y, y'\in Y,\ d_{\gamma}(y, y') = \max(d_{O}(q(y), q(y')), \gamma d_{\gamma}(\tau(y), \tau(y'))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/BellmanMaxEquation.discounted_prediction_distance_bellman` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an update, a readout, and a nonnegative real discrepancy bounded by D. For a discount factor gamma in (0, 1], the discounted prediction distance is the supremum over update times of gamma to that time times the observed discrepancy.

The time-zero term gives the current discrepancy. Every positive-time term factors as gamma times the corresponding term after one update. Boundedness supplies the conditionally complete suprema, and the two families give the displayed maximum.

Loogle found the exact Real.mul_iSup_of_nonneg declaration used to move gamma through the shifted supremum. Its complete-lattice sup_iSup_nat_succ result does not apply to Real. LeanSearch returned nearby supremum and fixed-point results but no full-statement match; repository and formalization-record searches found no duplicate.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/BellmanMaxEquation.discounted_prediction_distance_bellman`
