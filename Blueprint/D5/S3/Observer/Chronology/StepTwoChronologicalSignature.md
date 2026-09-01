# Step-Two Chronological Signature

## Abstract

Chronological words form a step-two signature monoid whose doubled logarithmic coordinate obeys the degree-two BCH law.

**Definition 1.1 (Step-two signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step-two signature stores degree one together with twice degree two, so the construction requires no division by two.

**Definition 1.2 (Chronological composition).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature.compose`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature.compose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composition adds degree one and inserts twice the ordered cross term from the left word to the right word at degree two.

**Definition 1.3 (Single-event signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One event contributes its algebra value at degree one and its square to doubled degree two.

**Definition 1.4 (Chronological word signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature of a list composes single-event signatures from left to right in operational chronology.

**Theorem 1.5 (Step-two Chen identity).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_append`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signature of an earlier word followed by a later word is their chronological signature product.

**Theorem 1.6 (Degree one forgets chronology).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_degree_one`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_degree_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Degree one is the ordinary sum of all observed event values and is therefore insensitive to their order.

**Definition 1.7 (Doubled degree-two Magnus coordinate).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the square of degree one from doubled degree two extracts the doubled logarithmic coordinate.

**Theorem 1.8 (Degree-two BCH law).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_mul`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic coordinate of a product is the sum of the two coordinates plus the commutator of their degree-one parts.

**Theorem 1.9 (Chronological BCH append law).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_append`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining Chen concatenation with the logarithmic coordinate gives the step-two BCH formula for two event words.

**Theorem 1.10 (Two-event Magnus coordinate is the commutator).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_commutator`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a chronology containing exactly two events, the doubled degree-two logarithmic coordinate is their ring commutator.

**Theorem 1.11 (Two-event orientation reversal).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_swap`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing two events negates the degree-two chronological defect.

**Theorem 1.12 (Commuting events have zero defect).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_zero_of_commute`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_zero_of_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A commuting event pair has no degree-two chronological memory.

## References

- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature.compose`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_append`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_degree_one`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_mul`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_append`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_commutator`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_swap`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_zero_of_commute`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../HiddenFlow/ProjectionCommutatorIdentity.md)
