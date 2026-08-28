# Quaternary Residue Coordinate Dimension

## Abstract

The four-state residue carrier has three explicit pair collisions and statistical dimension three.

**Theorem 1.1 (Every fixed coordinate pair is incomplete on the four-state carrier).**

$$\operatorname{MergesOn}\left(quaternaryCarrier, \{q2, q3\}, state15, state21\right) \land \left(\operatorname{MergesOn}\left(quaternaryCarrier, \{q2, q5\}, state0, state10\right) \land \left(\operatorname{MergesOn}\left(quaternaryCarrier, \{q3, q5\}, state0, state15\right) \land \operatorname{statisticalDimensionOn}\left(quaternaryCarrier\right) = 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/QuaternaryResidueCoordinateDimension.quaternary_statistical_dimension_eq_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem is stated directly on the finite residue-state carrier {0,10,15,21}; it has no ambient-state carrier parameter.

On this carrier, q2 with q3 merges 15 with 21, q2 with q5 merges 0 with 10, and q3 with q5 merges 0 with 15. These three public clauses force every two-coordinate selection to be incomplete.

All three coordinates are jointly injective on the same carrier. Together with the three collision clauses, this makes the least complete coordinate count exactly three.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/QuaternaryResidueCoordinateDimension.quaternary_statistical_dimension_eq_three`
- Dependency: [D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension](ResidueCoordinateDimension.md)
