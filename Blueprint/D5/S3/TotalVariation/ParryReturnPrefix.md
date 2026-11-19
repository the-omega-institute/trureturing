# Raw windows under arbitrary return-duration weights

## Abstract

Finite relation prefixes under independent return-duration weights.

**Theorem 1.1 (A raw prefix carries a duration tail factor).**

Lean statement: `D5/S3/TotalVariation/ParryReturnPrefix.iid_return_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryReturnPrefix.iid_return_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take any measure on native admissible relation paths whose complete return-duration cylinder masses factor with common weights on Fin k. A raw window specifying a finite list of complete returns and then j consecutive true bits has mass equal to the completed-return product times the tail mass of durations strictly greater than j.

After the specified returns, the next j bits are true exactly when the next return takes more than j steps. Partition the event by that next duration. The resulting cylinders are measurable and disjoint. Finite additivity and the assumed cylinder products give the formula.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryReturnPrefix.iid_return_prefix`
- Dependency: [D5/S3/TotalVariation/ParryFirstReturn](ParryFirstReturn.md)
