# Scalar perturbation of sorted singular values

## Abstract

Scalar perturbation of sorted singular values.

**Theorem 1.1 (Scalar perturbation of sorted singular values).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation.singularValuesSorted_add_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation.singularValuesSorted_add_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every square complex matrix Y, scalar z and decreasing index j, s_j(Y+zI) is at most s_j(Y)+|z|. The spectral subspace of the perturbed Gram matrix meets the subspace where the original Gram form is small; the vector triangle inequality then bounds the selected singular value.

**Theorem 1.2 (Real scalar shifts of a Hermitian spectrum).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation.eigenvalues_zero_add_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation.eigenvalues_zero_add_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

Adding rI to a Hermitian matrix adds r to every decreasing eigenvalue. Two complementary spectral subspace comparisons prove both directions, including repeated eigenvalues.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation.eigenvalues_zero_add_scalar`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation.singularValuesSorted_add_scalar`
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Schatten/SingularValueOrder.md)
