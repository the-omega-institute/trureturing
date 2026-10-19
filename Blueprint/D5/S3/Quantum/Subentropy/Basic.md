# Determinant-integral subentropy

## Abstract

Subentropy through a determinant integral, with rectangular Gram and isometric invariance.

All index types are finite with decidable equality. The ordinary complex matrix underlying a canonical density state is obtained with CStarMatrix.ofMatrix.symm. The integral is a real Lebesgue integral over the open positive half-line. Statements concerning arbitrary matrices assert algebraic invariance; the physical subentropy interpretation is restricted to positive matrices of trace one.

**Definition 1.1 (The determinant kernel).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.subentropyKernel`

*Formalization.* `D5/S3/Quantum/Subentropy/Basic.subentropyKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For t>0, K(A,t)=t/(1+t)−1/Re det(I+A/t). On a diagonal matrix with entries p, the reciprocal determinant is the product of t/(t+p_i).

**Definition 1.2 (The determinant integral).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy`

*Formalization.* `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

Q(A) is the integral of K(A,t) over t>0. This determinant representation handles zero eigenvalues and repeated eigenvalues directly.

**Definition 1.3 (Subentropy of a density state).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.subentropy`

*Formalization.* `D5/S3/Quantum/Subentropy/Basic.subentropy` (`✓ std3`).

*Citation.* Richard Jozsa, Daniel Robb, William K. Wootters (1994). *Lower bound for accessible information in quantum mechanics*. DOI: [10.1103/PhysRevA.49.668](https://doi.org/10.1103/PhysRevA.49.668). URL: <https://doi.org/10.1103/PhysRevA.49.668>.

*Commentary.*

Subentropy is evaluated on the ordinary matrix underlying the canonical DensityState. The determinant-integral representation is a repository derivation of the spectral quantity introduced by Jozsa, Robb and Wootters and studied by Datta and collaborators. The positive simple-spectrum formula is proved in SpectralFormula, and continuity on the full density-matrix domain is proved in DensityKernel.

**Theorem 1.4 (Rectangular Gram kernels).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.kernel_rectangular_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/Basic.kernel_rectangular_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For every rectangular complex matrix V and every real t, the kernels of V*V and VV* coincide. The determinant identity det(I+AB)=det(I+BA) proves this without a positivity, invertibility or trace hypothesis.

**Theorem 1.5 (Rectangular Gram invariance).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_rectangular_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_rectangular_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

Integration of the pointwise kernel identity gives Q(V*V)=Q(VV*) in arbitrary finite rectangular dimensions.

**Theorem 1.6 (Isometric embedding invariance).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_isometric_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_isometric_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

If J*J=I, then Q(JAJ*)=Q(A). The proof uses the rectangular determinant identity with factors JA and J*, and thus does not require a matrix square root.

**Theorem 1.7 (Pure states have zero subentropy).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_pure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

If the squared complex norm of v is one, its rank-one matrix vv* has subentropy zero. Its scalar Gram matrix is the one-dimensional identity, whose determinant kernel vanishes on the positive half-line.

**Theorem 1.8 (Classical product kernel).**

Lean statement: `D5/S3/Quantum/Subentropy/Basic.kernel_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/Basic.kernel_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For a real vector p and t nonzero, the kernel of diagonal p is t/(1+t) minus the product of t/(t+p_i). No positivity assumptions enter this algebraic identity.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.kernel_diagonal`
- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.kernel_rectangular_gram`
- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy`
- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_isometric_embedding`
- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_pure`
- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.matrixSubentropy_rectangular_gram`
- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.subentropy`
- Truth anchor: `D5/S3/Quantum/Subentropy/Basic.subentropyKernel`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
