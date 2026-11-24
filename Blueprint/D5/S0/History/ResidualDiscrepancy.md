# Residual Discrepancies

## Abstract

A discrepancy is residual exactly when observed and expected readings differ.

**Theorem 1.1 (A residual discrepancy is a nonzero difference).**

$$\operatorname{IsResidual}(expected, observed) \iff observed \neq expected$$

*Proof.* Machine-checked in Lean as `D5/S0/History/ResidualDiscrepancy.residual_iff_observed_ne_expected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For readings in any additive group, the residual discrepancy is the observed value minus the expected value. It is residual exactly when that difference is nonzero. The theorem therefore identifies the source atom's residual condition with the direct statement that the two readings differ; no order, norm, or numeric representation is assumed.

Adding the expected reading back on the right of the difference recovers the observed reading. If the difference vanishes, that recovery forces both readings to agree. Equal readings give zero by the inverse law.

## References

- Truth anchor: `D5/S0/History/ResidualDiscrepancy.residual_iff_observed_ne_expected`
