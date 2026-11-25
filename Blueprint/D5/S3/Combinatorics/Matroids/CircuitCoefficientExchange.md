# Exchanging a Coefficient Sector

## Abstract

One coefficient acts in its own sector of a stable submodule of alternating forms.

**Theorem 1.1 (Exchanging a Coefficient Sector).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitCoefficientExchange.coefficient_family_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitCoefficientExchange.coefficient_family_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use alternating forms of degree d in a common integral basis with ordered index set I. Fix a finite subset A of I, a selected d-element subset F of I and a finite family of prior d-element subsets of I. The projection keeps precisely the coefficients indexed by d-element subsets G with G intersect A equal to F intersect A. Assume the projection preserves the submodule K of forms and each prior subset has a different intersection with A from F. Let P be the common kernel of all prior coefficient readouts in K, and let Q be the kernel of the F readout in K. There is an integer-linear isomorphism from K times the intersection of P and Q to P times Q. Exchange the complementary sector of two forms while holding the selected sector of each form in place. This operation is an integral linear involution. Each prior coefficient reads the exchanged part, while the new coefficient reads the part held in place. The unrestricted and jointly restricted modules therefore have the same product as the two separately restricted modules.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitCoefficientExchange.coefficient_family_exchange`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates](CircuitPassiveCoordinates.md)
