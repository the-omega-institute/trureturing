# Step-Two Chronological Signature

## Abstract

Step-two signatures obey Chen concatenation and the degree-two BCH law.

**Definition 1.1 (Step-two signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A step-two signature stores degree one together with twice degree two, so the construction requires no division by two.

**Definition 1.2 (Single-event signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One event contributes its algebra value at degree one and its square to doubled degree two.

**Definition 1.3 (Chronological word signature).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature of a list composes single-event signatures from left to right in operational chronology.

**Theorem 1.4 (Step-two Chen identity).**

$$\forall f, P, S, \operatorname{chronologicalSignature}(f, \operatorname{append}(P, S)) = \operatorname{chronologicalSignature}(f, P) \cdot \operatorname{chronologicalSignature}(f, S).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signature of an earlier word followed by a later word is their chronological signature product.

**Theorem 1.5 (Degree one forgets chronology).**

$$\forall f, L, \operatorname{degreeOne}(\operatorname{chronologicalSignature}(f, L)) = \operatorname{sum}(\operatorname{map}(f, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_degree_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Degree one is the ordinary sum of all observed event values and is therefore insensitive to their order.

**Definition 1.6 (Doubled degree-two Magnus coordinate).**

Lean statement: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo`

*Formalization.* `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the square of degree one from doubled degree two extracts the doubled logarithmic coordinate.

**Theorem 1.7 (Degree-two BCH law).**

$$\forall a, b, \operatorname{doubledMagnusDegreeTwo}(a \cdot b) = \operatorname{doubledMagnusDegreeTwo}(a) + \operatorname{doubledMagnusDegreeTwo}(b) + \operatorname{commutator}(\operatorname{degreeOne}(a), \operatorname{degreeOne}(b)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic coordinate of a product is the sum of the two coordinates plus the commutator of their degree-one parts.

**Theorem 1.8 (Chronological BCH append law).**

$$\begin{gathered}\forall f, P, S:\\{}\operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, \operatorname{append}(P, S))) = \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, P)) + \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, S)) + \operatorname{commutator}(\operatorname{degreeOne}(\operatorname{chronologicalSignature}(f, P)), \operatorname{degreeOne}(\operatorname{chronologicalSignature}(f, S))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining Chen concatenation with the logarithmic coordinate gives the step-two BCH formula for two event words.

**Theorem 1.9 (Two-event Magnus coordinate is the commutator).**

$$\forall f, p, q, \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [p, q])) = \operatorname{commutator}(\operatorname{f}(p), \operatorname{f}(q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a chronology containing exactly two events, the doubled degree-two logarithmic coordinate is their ring commutator.

**Theorem 1.10 (Two-event orientation reversal).**

$$\forall f, p, q, \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [q, p])) = -\operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [p, q])).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing two events negates the degree-two chronological defect.

**Theorem 1.11 (Commuting events have zero defect).**

$$\forall f, p, q, \operatorname{f}(p) \cdot \operatorname{f}(q) = \operatorname{f}(q) \cdot \operatorname{f}(p) \Rightarrow \operatorname{doubledMagnusDegreeTwo}(\operatorname{chronologicalSignature}(f, [p, q])) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_zero_of_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A commuting event pair has no degree-two chronological memory.

## References

- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.StepTwoSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronologicalSignature`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_append`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.chronological_signature_degree_one`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubledMagnusDegreeTwo`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_append`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_degree_two_mul`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_commutator`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_eq_zero_of_commute`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.doubled_magnus_two_events_swap`
- Truth anchor: `D5/S3/Observer/Chronology/StepTwoChronologicalSignature.eventSignature`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../HiddenFlow/ProjectionCommutatorIdentity.md)
