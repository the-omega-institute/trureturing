# Finite

## Abstract

Second peak SecondPeakA2: Finite

Thirty-two exact rows and the unbounded q-two dyadic selector cover p in {4,8,16,32}, q in {2,4,8,16,32}, h in {1,2}. For q=2 and p in {4,8,16,32}, QTwoStructural supplies strict physical stocks, proper bit inclusion and every old/new window for both h values. The remaining rows check the same conditions directly. The infinite sectors are proved in Large and Small.

**Definition 1.1 (BoundaryRow).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.BoundaryRow`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.BoundaryRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition BoundaryRow in the source module; Thirty-two exact rows and the unbounded q-two dyadic selector cover p in {4,8,16,32}, q in {2,4,8,16,32}, h in {1,2}. For q=2 and p in {4,8,16,32}, QTwoStructural supplies strict physical stocks, proper bit inclusion and every old/new window for both h values. The remaining rows check the same conditions directly. The infinite sectors are proved in Large and Small.

**Definition 1.2 (BoundaryRow.Check).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.Check`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.Check` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition BoundaryRow.Check in the source module; Thirty-two exact rows and the unbounded q-two dyadic selector cover p in {4,8,16,32}, q in {2,4,8,16,32}, h in {1,2}. For q=2 and p in {4,8,16,32}, QTwoStructural supplies strict physical stocks, proper bit inclusion and every old/new window for both h values. The remaining rows check the same conditions directly. The infinite sectors are proved in Large and Small.

**Definition 1.3 (boundaryRows).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.boundaryRows`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.boundaryRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition boundaryRows in the source module; Thirty-two exact rows and the unbounded q-two dyadic selector cover p in {4,8,16,32}, q in {2,4,8,16,32}, h in {1,2}. For q=2 and p in {4,8,16,32}, QTwoStructural supplies strict physical stocks, proper bit inclusion and every old/new window for both h values. The remaining rows check the same conditions directly. The infinite sectors are proved in Large and Small.

**Theorem 1.4 (finite_exists).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.finite_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.finite_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem finite_exists (p q h : ℕ)     (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32)     (hq : q=2 ∨ q=4 ∨ q=8 ∨ q=16 ∨ q=32) (hh : h=1 ∨ h=2) :     ∃ v m M : ℕ, ∃ before : Bool, Good p q h v m M before

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.BoundaryRow`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.Check`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.boundaryRows`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Finite.finite_exists`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural](QTwoStructural.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Small](Small.md)
