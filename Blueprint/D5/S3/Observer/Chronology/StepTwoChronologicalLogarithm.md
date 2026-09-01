# Step-Two Chronological Logarithm

## Abstract

Step-two signature coordinates are multiplicatively equivalent to the truncated BCH law, with an explicit antipode.

**Definition 1.1 (Step-two logarithmic coordinate).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate stores degree one and the doubled degree-two Lie component.

**Definition 1.2 (Chronological logarithm).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLog`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithm subtracts the square of degree one from doubled degree two.

**Definition 1.3 (Step-two exponential).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalExp`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalExp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponential restores signature coordinates by adding the square of degree one.

**Theorem 1.4 (Exponential after logarithm).**

$$\forall a, \operatorname{chronologicalExp}(\operatorname{chronologicalLog}(a)) = a.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_exp_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exponentiating a chronological logarithm exactly recovers its signature.

**Theorem 1.5 (Logarithm after exponential).**

$$\forall c, \operatorname{chronologicalLog}(\operatorname{chronologicalExp}(c)) = c.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the logarithm of a step-two exponential exactly recovers its coordinate.

**Theorem 1.6 (Multiplicative BCH law).**

$$\forall a, b, \operatorname{chronologicalLog}(a \cdot b) = \operatorname{chronologicalLog}(a) \cdot \operatorname{chronologicalLog}(b).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete logarithm converts Chen composition into the truncated BCH product.

**Definition 1.7 (Signature-BCH multiplicative equivalence).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLogMulEquiv`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLogMulEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Logarithm and exponential form an explicit multiplicative equivalence of the two coordinate systems.

**Definition 1.8 (Signature antipode).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signatureAntipode`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signatureAntipode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit inverse negates degree one and applies the transported quadratic correction at degree two.

**Theorem 1.9 (Antipode in logarithmic coordinates).**

$$\forall a, \operatorname{chronologicalLog}(\operatorname{signatureAntipode}(a)) = \operatorname{inverse}(\operatorname{chronologicalLog}(a)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_antipode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm maps the signature antipode to coordinatewise negation.

**Theorem 1.10 (Antipode reverses multiplication).**

$$\forall a, b, \operatorname{signatureAntipode}(a \cdot b) = \operatorname{signatureAntipode}(b) \cdot \operatorname{signatureAntipode}(a).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signature_antipode_mul_rev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antipode of a chronological product is the reversed product of the two antipodes.

## References

- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalExp`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLog`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLogMulEquiv`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_exp_log`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_antipode`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_exp`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_mul`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signatureAntipode`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signature_antipode_mul_rev`
- Dependency: [D5/S3/Observer/Chronology/StepTwoChronologicalSignature](StepTwoChronologicalSignature.md)
