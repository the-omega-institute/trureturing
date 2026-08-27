# Sharp-Measurement Compatibility

## Abstract

Joint sharp measurements are exactly pairwise commuting, while general effects need not commute.

**Theorem 1.1 (Sharp measurements are jointly measurable exactly when they commute).**

$$\forall n \in \operatorname{Type}\left(\right), A \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] [\operatorname{Fintype}\left(A\right)] [\operatorname{Fintype}\left(B\right)], \forall P: A \to \operatorname{Matrix}\left(n, n, \mathbb{C}\right), Q: B \to \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\\{}\begin{gathered}\operatorname{IsRecordMeasurement}\left(P\right) \land \operatorname{IsRecordMeasurement}\left(Q\right) \Rightarrow\\{}(\left(\exists R \in A \times B \to \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{IsRecordMeasurement}\left(R\right) \land \left(\left(\forall a \in A,\; P\left(a\right) = \sum_{b \in B} R\left(\operatorname{pair}\left(a, b\right)\right)\right) \land \left(\forall b \in B,\; Q\left(b\right) = \sum_{a \in A} R\left(\operatorname{pair}\left(a, b\right)\right)\right)\right)\right) \Leftrightarrow \left(\forall a \in A, b \in B,\; P\left(a\right) \cdot Q\left(b\right) = Q\left(b\right) \cdot P\left(a\right)\right)) \land\\{}\operatorname{let} zPlus: \operatorname{QubitState}\left(\right) := \operatorname{vec2}\left(1, 0\right); \\{}\operatorname{let} zMinus: \operatorname{QubitState}\left(\right) := \operatorname{vec2}\left(0, 1\right); \\{}\operatorname{let} xPlus: \operatorname{QubitState}\left(\right) := \operatorname{vec2}\left(1, 1\right); \\{}\operatorname{let} xMinus: \operatorname{QubitState}\left(\right) := \operatorname{vec2}\left(1, -1\right); \\{}\operatorname{let} joint: Bool \times Bool \to \operatorname{QubitMatrix}\left(\right), joint\left(\operatorname{pair}\left(false, false\right)\right) = \frac{1}{2} \cdot \operatorname{vecMulVec}\left(zPlus, \operatorname{star}\left(zPlus\right)\right), joint\left(\operatorname{pair}\left(false, true\right)\right) = \frac{1}{4} \cdot \operatorname{vecMulVec}\left(xPlus, \operatorname{star}\left(xPlus\right)\right), joint\left(\operatorname{pair}\left(true, false\right)\right) = \frac{1}{4} \cdot \operatorname{vecMulVec}\left(xMinus, \operatorname{star}\left(xMinus\right)\right), joint\left(\operatorname{pair}\left(true, true\right)\right) = \frac{1}{2} \cdot \operatorname{vecMulVec}\left(zMinus, \operatorname{star}\left(zMinus\right)\right); \\{}\operatorname{let} first: Bool \to \operatorname{QubitMatrix}\left(\right), \forall a: Bool, first\left(a\right) = \sum_{b \in Bool} joint\left(\operatorname{pair}\left(a, b\right)\right); \\{}\operatorname{let} second: Bool \to \operatorname{QubitMatrix}\left(\right), \forall b: Bool, second\left(b\right) = \sum_{a \in Bool} joint\left(\operatorname{pair}\left(a, b\right)\right); \\{}\left(\forall o \in Bool \times Bool,\; \operatorname{PosSemidef}\left(joint\left(o\right)\right)\right) \land \left(\sum_{o \in Bool \times Bool} joint\left(o\right) = 1 \land \left(\left(\neg \operatorname{IsRecordMeasurement}\left(first\right)\right) \land \left(\left(\neg \operatorname{IsRecordMeasurement}\left(second\right)\right) \land first\left(false\right) \cdot second\left(false\right) \ne second\left(false\right) \cdot first\left(false\right)\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/SharpMeasurementCompatibility.sharp_measurement_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two arbitrary finite record measurements admit a joint record measurement with the stated marginals exactly when every effect from the first family commutes with every effect from the second.

The forward direction expands both marginals and uses orthogonality of distinct joint outcomes. The reverse direction constructs each joint outcome as the product of the commuting effects.

The final clauses give one shared positive normalized qubit measurement. Both of its marginals are nonsharp, and their false-false effects do not commute. This records the source's contrast with general nonsharp effects on the same public construction.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/SharpMeasurementCompatibility.sharp_measurement_compatibility`
- Dependency: [D5/S3/Observer/Conditioning](../../Observer/Conditioning.md)
- Dependency: [D5/S3/Quantum/QubitWitnesses](../QubitWitnesses.md)
