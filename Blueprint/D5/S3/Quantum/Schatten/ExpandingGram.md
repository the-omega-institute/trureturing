# Expanding square matrices and their singular values

## Abstract

Expanding square matrices and their singular values.

**Theorem 1.1 (Expansion implies invertibility).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingGram.expanding_isUnit_det`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ExpandingGram.expanding_isUnit_det` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

If a complex square matrix T satisfies T*T−I positive semidefinite, then det(T) is a unit. Its Gram matrix is positive definite, so T is invertible. The assertion includes the empty matrix.

**Theorem 1.2 (Expansion of the adjoint).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingGram.expanding_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ExpandingGram.expanding_adjoint` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

If T*T−I is positive semidefinite for a complex square T, then TT*−I is positive semidefinite as well. Singular-value decomposition transfers the lower bound from one Gram matrix to the other.

**Theorem 1.3 (Right multiplication by an expanding matrix).**

Lean statement: `D5/S3/Quantum/Schatten/ExpandingGram.expanding_right_singularValuesSorted`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ExpandingGram.expanding_right_singularValuesSorted` (`✓ std3`). ∎

*Citation.* Rajendra Bhatia (1997). *Matrix Analysis*. DOI: [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). URL: <https://doi.org/10.1007/978-1-4612-0653-8>.

*Commentary.*

For every complex square A and every T with T*T−I positive semidefinite, sᵢ(A)≤sᵢ(AT) for every decreasing singular-value index i. Positivity of A(TT*−I)A* and Gram-order monotonicity prove the comparison; A need not be invertible.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingGram.expanding_adjoint`
- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingGram.expanding_isUnit_det`
- Truth anchor: `D5/S3/Quantum/Schatten/ExpandingGram.expanding_right_singularValuesSorted`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](SingularValueOrder.md)
