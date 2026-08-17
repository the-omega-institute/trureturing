# Finite Prediction Truncation

## Abstract

Finite Bellman prediction distances have an exact maximum formula and geometric error.

**Theorem 1.1 (Finite prediction truncation has a geometric error bound).**

$$\forall \gamma\in(0, 1], (\forall a, b\in O,\ 0\leq d_{O}(a, b)\leq D) \Rightarrow \forall m\in \mathbb{N},\ \forall y, y'\in Y,\ p_{m+1}(y, y') = \max_{0 \leq k \leq m} \gamma^{k} d_{O}(q(\tau^{k}(y)), q(\tau^{k}(y'))),\ 0\leq d_{\gamma}(y, y')-p_{m+1}(y, y') \leq \gamma^{m+1} D.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/FinitePredictionTruncation.finite_prediction_truncation_formula_and_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start the finite prediction distance at zero and apply the Bellman maximum operator m plus one times. Assume the output discrepancy is nonnegative and bounded by D, and gamma lies in (0, 1]. The iterate is the maximum of the discounted discrepancies at times zero through m.

Induction splits the finite maximum into its time-zero term and its discounted tail. Comparing the same split with the infinite Bellman equation shows that the finite iterate is below the full distance. The imported max-subtraction bound contracts the remaining error by gamma at each step.

Loogle returned named finite-supremum support declarations. LeanSearch returned related finite-supremum and geometric truncation results but no full theorem match. After type inspection, the Lean proof imports and applies max_sub_max_le_max and the conditionally complete finite-supremum library lemmas; repository and formalization searches found no duplicate.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/FinitePredictionTruncation.finite_prediction_truncation_formula_and_error`
