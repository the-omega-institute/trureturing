# Step-Two Chronological Logarithm

## Abstract

Step-two chronological signatures are multiplicatively equivalent to the truncated BCH coordinate law, with an explicit division-free antipode.

**Definition 1.1 (Step-two logarithmic coordinate).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate stores degree one and the doubled degree-two Lie component.

**Definition 1.2 (Truncated BCH product).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm.bch`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm.bch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product adds both coordinates and inserts the commutator of the degree-one components.

**Definition 1.3 (Chronological logarithm).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLog`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithm subtracts the square of degree one from doubled degree two.

**Definition 1.4 (Step-two exponential).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalExp`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalExp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponential restores signature coordinates by adding the square of degree one.

**Theorem 1.5 (Exponential after logarithm).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_exp_log`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_exp_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exponentiating a chronological logarithm exactly recovers its signature.

**Theorem 1.6 (Logarithm after exponential).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_exp`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the logarithm of a step-two exponential exactly recovers its coordinate.

**Theorem 1.7 (Multiplicative BCH law).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_mul`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete logarithm converts Chen composition into the truncated BCH product.

**Definition 1.8 (Signature-BCH multiplicative equivalence).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLogMulEquiv`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLogMulEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Logarithm and exponential form an explicit multiplicative equivalence of the two coordinate systems.

**Definition 1.9 (Signature antipode).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signatureAntipode`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signatureAntipode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit inverse negates degree one and applies the transported quadratic correction at degree two.

**Theorem 1.10 (Antipode in logarithmic coordinates).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_antipode`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_antipode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm maps the signature antipode to coordinatewise negation.

**Theorem 1.11 (Antipode reverses multiplication).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signature_antipode_mul_rev`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signature_antipode_mul_rev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antipode of a chronological product is the reversed product of the two antipodes.

## References

- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.StepTwoLogarithm.bch`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLog`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalExp`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_exp_log`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_exp`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_mul`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronologicalLogMulEquiv`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signatureAntipode`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.chronological_log_antipode`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm.signature_antipode_mul_rev`
- Dependency: [D5/S3/Observer/Chronology/StepTwoChronologicalSignature](StepTwoChronologicalSignature.md)
