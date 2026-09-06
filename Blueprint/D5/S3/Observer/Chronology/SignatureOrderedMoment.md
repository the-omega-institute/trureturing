# Signature and Ordered-Moment Semantics

## Abstract

For every finite word, doubled degree two is its event-square sum plus twice its ordered-pair moment.

**Theorem 1.1 (The stored coordinate for all finite words).**

$$\forall A, E, \operatorname{Semiring}\left(A\right), o:E\to A, w:\operatorname{List}\left(E\right), \operatorname{doubledDegreeTwo}\left(\operatorname{chronologicalSignature}\left(o, w\right)\right)=\operatorname{sum}\left(\operatorname{map}\left(e\mapsto\operatorname{o}\left(e\right)\cdot \operatorname{o}\left(e\right), w\right)\right)+2\cdot \operatorname{orderedPairMoment}\left(\operatorname{map}\left(o, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/SignatureOrderedMoment.chronological_signature_doubledDegreeTwo_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A and E are arbitrary types, A is a possibly noncommutative semiring, o maps E to A, and w is a finite list over E. The diagonal term sums o(e)o(e) over the occurrences in w; M2 is the existing orderedPairMoment on the value list. The formula accounts for both repeated events and ordered cross terms.

**Theorem 1.2 (Magnus is the difference between the two orientations).**

$$\forall A, E, \operatorname{Ring}\left(A\right), o:E\to A, w:\operatorname{List}\left(E\right), \operatorname{doubledMagnusDegreeTwo}\left(\operatorname{chronologicalSignature}\left(o, w\right)\right)=\operatorname{orderedPairMoment}\left(\operatorname{map}\left(o, w\right)\right)-\operatorname{orderedPairMoment}\left(\operatorname{reverse}\left(\operatorname{map}\left(o, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/SignatureOrderedMoment.doubledMagnusDegreeTwo_eq_orderedPairMoment_sub_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary types A and E, a ring A, o : E to A, and w : List E, the corrected coordinate is the forward ordered-pair moment minus the moment of the reversed value list. The proof uses the all-word square decomposition, which separates event squares from both ordered orientations without assuming commutativity or dividing by two.

## References

- Truth anchor: `D5/S3/Observer/Chronology/SignatureOrderedMoment.chronological_signature_doubledDegreeTwo_eq`
- Truth anchor: `D5/S3/Observer/Chronology/SignatureOrderedMoment.doubledMagnusDegreeTwo_eq_orderedPairMoment_sub_reverse`
- Dependency: [D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape](PrimeGoldenThirdOrderChronologyEscape.md)
