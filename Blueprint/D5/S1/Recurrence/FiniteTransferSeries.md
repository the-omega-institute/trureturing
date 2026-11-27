# Generating series of finite matrix observations

## Abstract

Finite matrix powers give an exact formal resolvent with a unit-constant polynomial denominator.

**Definition 1.1 (Shifted series of matrix powers).**

Lean statement: `D5/S1/Recurrence/FiniteTransferSeries.walks`

*Formalization.* `D5/S1/Recurrence/FiniteTransferSeries.walks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite index type with decidable equality, a rational square matrix M, and rational vectors u and v, walks(M,u,v) is a formal power series with zero constant coefficient and coefficient uᵀM^m v at degree m+1.

**Theorem 1.2 (Matrix inverse and polynomial denominator).**

Lean statement: `D5/S1/Recurrence/FiniteTransferSeries.walks_resolvent`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FiniteTransferSeries.walks_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set A = I−XM over the rational polynomial ring and B = I−XM over the rational formal power series ring. The constant coefficient of det A is one. The shifted series is X·uᵀB⁻¹v, and multiplying it by det A gives the polynomial X·uᵀadj(A)v. The coefficient of degree m of the entrywise matrix series is M^m. Multiplication by B has constant coefficient I and cancels every higher coefficient by the matrix power law. The determinant condition gives a formal inverse, so the coefficient series is that inverse. The adjugate identity then clears the denominator.

## References

- Truth anchor: `D5/S1/Recurrence/FiniteTransferSeries.walks`
- Truth anchor: `D5/S1/Recurrence/FiniteTransferSeries.walks_resolvent`
