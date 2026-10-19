# Balanced inverse-adjoint averages are expanding

## Abstract

Balanced inverse-adjoint averages are expanding.

The balanced diagonal-matrix and inverse average in Bhatia–Kittaneh–Li (1997), §4, is a related method; here the inverse adjoint permits arbitrary invertible complex W.

**Definition 1.1 (A balanced average).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingAverage.inverseAdjointAverage`

*Formalization.* `D5/S3/Quantum/Schatten/ExpandingAverage.inverseAdjointAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex square matrix W and real t, inverseAdjointAverage W t is Tₜ=(tW+t⁻¹(W⁻¹)*)/2. Expansion is asserted when W is invertible and t is positive.

**Theorem 1.2 (Expansion of the balanced average).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingAverage.inverseAdjointAverage_expanding`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ExpandingAverage.inverseAdjointAverage_expanding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For invertible W and positive t, Tₜ*Tₜ−I is positive semidefinite. Indeed, with Sₜ=tW−t⁻¹(W⁻¹)*, the identity Tₜ*Tₜ−I=Sₜ*Sₜ/4 follows because both mixed products are identities. Hence every singular value of Tₜ is at least one.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingAverage.inverseAdjointAverage`
- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingAverage.inverseAdjointAverage_expanding`
