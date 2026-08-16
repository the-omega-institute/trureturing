# Completion Diagonal Naturality

## Abstract

Projection to the complete future quotient commutes with twisted diagonalization.

**Theorem 1.1 (The complete quotient projection commutes with twisted diagonalization).**

$$\forall A, Y, O: \operatorname{Type},\ tau: Y \to Y, q: Y \to O,\ E: A \to \left(A \to Y\right),\ (a \mapsto [tau(E(a)(a))]) = \operatorname{diagonal}\left(\operatorname{quotientUpdate}\left(tau, q\right), (a, b \mapsto [E(a)(b)])\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/CompletionDiagonalNaturality.completion_quotient_diagonal_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau update a state type Y, let q read Y into O, and let E be a Y-valued table on an address type A. The complete itinerary sends a state to all of its future q-readouts. Write brackets for the class in the quotient by equality of complete itineraries, and let Uq be the canonical update transported to that quotient.

Projecting the tau-twisted diagonal of E pointwise gives exactly the Uq-twisted diagonal of the pointwise projected table. This is the single equality asserted by the source theorem; no clause is dropped and no commutation hypothesis is added.

The proof derives the quotient projection's commutation with tau from the frozen complete-itinerary construction, then applies the exact repository theorem coordinate_restriction_naturality at the identity address embedding. The result needs no finiteness assumption, so it specializes to the source section's finite state setting.

Repository search found those two supporting declarations but no duplicate of this quotient diagonal identity. Loogle found the exact Quotient.map_mk computation; the existing transported quotient update is reused instead. LeanSearch's query endpoint returned HTTP 404.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/CompletionDiagonalNaturality.completion_quotient_diagonal_naturality`
- Dependency: [D5/S0/Diagonal/Naturality/CoordinateRestrictionNaturality](../../../S0/Diagonal/Naturality/CoordinateRestrictionNaturality.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](ItineraryCompletion.md)
