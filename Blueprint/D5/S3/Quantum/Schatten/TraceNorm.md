# The trace norm and its two-dimensional formula

## Abstract

The trace norm supplies a unitarily invariant norm in every finite complex dimension, with an exact determinant formula in dimension two.

**Definition 1.1 (The trace norm as a unitarily invariant norm).**

Lean statement: `D5/S3/Quantum/Schatten/TraceNorm.traceNormUINorm`

*Formalization.* `D5/S3/Quantum/Schatten/TraceNorm.traceNormUINorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mostafa Hayajneh; Saja Hayajneh; Fuad Kittaneh (2018). *On some classical trace inequalities and a new Hilbert–Schmidt norm inequality*. DOI: [10.7153/mia-2018-21-81](https://doi.org/10.7153/mia-2018-21-81). URL: <https://doi.org/10.7153/mia-2018-21-81>.

*Commentary.*

For every natural dimension n, the norm value of a complex n by n matrix A is Re Tr sqrt(A* A). The construction supplies nonnegativity, vanishing exactly at zero, the triangle inequality, complex absolute homogeneity and invariance under left and right unitary multiplication. The existing finite trace-distance laws supply the triangle inequality and a variational formula over unitary matrices. Cyclicity of the trace and multiplication by inverse unitaries establish two-sided unitary invariance. The empty dimension is included.

**Theorem 1.2 (The determinant of the positive absolute value).**

Lean statement: `D5/S3/Quantum/Schatten/TraceNorm.det_transitionAbs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/TraceNorm.det_transitionAbs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mostafa Hayajneh; Saja Hayajneh; Fuad Kittaneh (2018). *On some classical trace inequalities and a new Hilbert–Schmidt norm inequality*. DOI: [10.7153/mia-2018-21-81](https://doi.org/10.7153/mia-2018-21-81). URL: <https://doi.org/10.7153/mia-2018-21-81>.

*Commentary.*

For every complex two by two matrix T, det sqrt(T* T) is the complex embedding of the nonnegative real number |det T|. Positivity of the Gram matrix allows the determinant to pass through its positive square root. Multiplicativity of the determinant and the adjoint determinant formula identify the resulting square root with |det T|. No invertibility or Hermitian assumption on T is needed.

**Theorem 1.3 (The square of the trace norm in dimension two).**

Lean statement: `D5/S3/Quantum/Schatten/TraceNorm.transitionMass_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/TraceNorm.transitionMass_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mostafa Hayajneh; Saja Hayajneh; Fuad Kittaneh (2018). *On some classical trace inequalities and a new Hilbert–Schmidt norm inequality*. DOI: [10.7153/mia-2018-21-81](https://doi.org/10.7153/mia-2018-21-81). URL: <https://doi.org/10.7153/mia-2018-21-81>.

*Commentary.*

For every complex two by two matrix T, (Re Tr sqrt(T* T))² equals frobSq(T)+2|det T|, where frobSq(T)=Re Tr(T* T) is its squared Frobenius norm. The two-dimensional trace-power identity applied to sqrt(T* T), together with its real trace, its square T* T and the absolute-determinant formula, proves the equality. The formula applies equally to non-Hermitian and singular matrices, and gives exact rational comparisons for the mixed-power counterexample.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/TraceNorm.det_transitionAbs`
- Truth anchor: `D5/S3/Quantum/Schatten/TraceNorm.traceNormUINorm`
- Truth anchor: `D5/S3/Quantum/Schatten/TraceNorm.transitionMass_sq`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/Schatten/UnitarilyInvariantNorm](UnitarilyInvariantNorm.md)
