# Finite Readout Fiber Diameter

## Abstract

A shared finite readout prefix gives a geometric prediction-distance bound.

**Theorem 1.1 (A finite readout fiber has geometrically small prediction diameter).**

$$0<\gamma\leq1, (\forall a,\ d_{O}(a, a)=0),\ (\forall a, b,\ d_{O}(a, b) \leq D),\ (\forall k \leq m,\ q(\tau^{k}(y))=q(\tau^{k}(y'))) \Rightarrow d_{\gamma}(y, y') \leq \gamma^{m+1} D.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter.finite_word_fiber_prediction_diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an update, a readout, and a real-valued output discrepancy that vanishes on the diagonal. Assume all discrepancies are at most D and the discount factor gamma lies in (0, 1]. If two states have the same readout at update times zero through m, their discounted prediction distance is at most gamma to the power m plus one times D.

For times through m, readout equality makes the discrepancy term zero. At every later time k, the global distance bound gives gamma to the power k times D, and geometric decay compares this with gamma to the power m plus one times D. Taking the supremum proves the claim.

Loogle and LeanSearch found no full finite-prefix diameter theorem. The Lean proof applies the exact library results ciSup_le and pow_le_pow_of_le_one; repository and digestion-record searches found no duplicate.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter.finite_word_fiber_prediction_diameter`
- Dependency: [D5/S3/Observer/MetricGeometry/BellmanMaxEquation](BellmanMaxEquation.md)
