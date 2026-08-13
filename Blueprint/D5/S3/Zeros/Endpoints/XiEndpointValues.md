# Xi Endpoint Values

## Abstract

The pole-removed completed-zeta xi reading has value one-half at both endpoints.

**Theorem 1.1 (Xi reading endpoint values equal one-half).**

$$\operatorname{xiReading}(0)=\frac{1}{2} \land \operatorname{xiReading}(1)=\frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/XiEndpointValues.xi_reading_endpoint_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint values are definitionally immediate from the frozen pole-removed xi reading: at zero and one, the factor s times s minus one vanishes, leaving one half.

This module records those values as an addressable certificate discharging the ledger claim. It asserts no additional pole or continuation clause.

## References

- Truth anchor: `D5/S3/Zeros/Endpoints/XiEndpointValues.xi_reading_endpoint_values`
- Dependency: [D5/S3/Zeros/CompletedZeta](../CompletedZeta.md)
