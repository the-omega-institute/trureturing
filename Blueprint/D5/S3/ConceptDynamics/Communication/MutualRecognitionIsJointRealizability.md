# Mutual Recognition as Joint Realizability

## Abstract

Mutual recognition is joint realizability by one admissible world; it neither requires equal concepts nor follows from separate realizability.

**Theorem 1.1 (Mutual recognition is simultaneous realization).**

$$\forall World \in Type, B1 \in Type, B2 \in Type, Adm \in \operatorname{Set}\left(World\right), C1 \in World \to B1, C2 \in World \to B2, b1 \in B1, b2 \in B2,\; \operatorname{MutuallyRecognized}\left(Adm, C1, C2, (b1, b2)\right) \Leftrightarrow \left(\exists w \in Adm,\; C1\left(w\right) = b1 \land C2\left(w\right) = b2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability.mutually_recognized_iff_joint_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pair of states is mutually recognized exactly when one admissible world produces the first state under the first concept and the second state under the second concept.

The two coordinates of a joint readout identify the component realizations. Conversely, component equalities at the same world identify the ordered pair, so the shared witness is the essential content of mutual recognition.

**Lemma 1.2 (Recognizing one pair does not equate the concepts).**

$$\exists C1 \in Bool \to Bool, C2 \in Bool \to Bool, b1 \in Bool, b2 \in Bool,\; C1 \ne C2 \land \operatorname{MutuallyRecognized}\left(\operatorname{univ}\left(Bool\right), C1, C2, (b1, b2)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the Boolean world space, take the first concept to be constantly false and the second to be the identity. The concepts differ at the true world, yet that world jointly realizes the pair (false, true).

Mutual recognition therefore asserts compatibility at one admissible world, not equality of the two readout functions on every world.

**Lemma 1.3 (Separate witnesses need not combine into a joint witness).**

$$\exists Adm \in \operatorname{Set}\left(Bool\right), C1 \in Bool \to Bool, C2 \in Bool \to Bool, b1 \in Bool, b2 \in Bool,\; \left(\exists w \in Adm,\; C1\left(w\right) = b1\right) \land \left(\left(\exists w \in Adm,\; C2\left(w\right) = b2\right) \land \left(\neg \operatorname{MutuallyRecognized}\left(Adm, C1, C2, (b1, b2)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability.separate_realizability_does_not_imply_mutual_recognition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let both concepts be the identity on the full Boolean world space. The false state is realized by the false world and the true state is realized by the true world, so both descriptions are separately realizable.

No single Boolean world can equal both false and true. Hence the pair (false, true) has no joint witness, showing that separate realizability omits the synchronization required for mutual recognition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts`
- Truth anchor: `D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability.mutually_recognized_iff_joint_witness`
- Truth anchor: `D5/S3/ConceptDynamics/Communication/MutualRecognitionIsJointRealizability.separate_realizability_does_not_imply_mutual_recognition`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
