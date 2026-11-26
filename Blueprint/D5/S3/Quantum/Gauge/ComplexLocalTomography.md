# Local tomography and real division algebras

## Abstract

Self-adjoint coordinates, real density matrices and complex product observables.

A real diagonal coefficient determines each diagonal entry. A scalar coefficient determines each strictly upper entry, and its adjoint determines the reflected lower entry. This yields explicit real bases by placing the scalar basis elements at those upper entries.

**Theorem 1.1 (Real symmetric dimension).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_realHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_realHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

There is one real coordinate per upper entry and per diagonal entry. The real dimension of the symmetric matrices of size n is n(n + 1)/2.

**Theorem 1.2 (Complex Hermitian dimension).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_complexHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_complexHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

Each strict upper entry has two real coordinates, in the scalar basis 1 and i. Including the diagonal, the real dimension is n squared.

**Theorem 1.3 (Quaternionic Hermitian dimension).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_quaternionHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_quaternionHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

Each strict upper entry has four real coordinates, in the scalar basis 1, i, j and k. Including the diagonal, the real dimension is n(2n − 1).

**Theorem 1.4 (Dimension multiplicativity).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.division_algebra_local_tomography_selection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.division_algebra_local_tomography_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

For both local sizes at least two, the real symmetric composite dimension exceeds the product of the local dimensions. The complex Hermitian dimensions multiply exactly, and the quaternionic Hermitian composite dimension is strictly smaller than the product of the local dimensions. Thus complex scalars are the unique choice among these three for dimension multiplicativity.

**Theorem 1.5 (Explicit complex tensor basis).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.tensorHermBasis_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.tensorHermBasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

The basis vector indexed by a pair of local indices is the Kronecker product of the corresponding local Hermitian basis vectors.

**Theorem 1.6 (Complex local tomography).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.span_tensor_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.span_tensor_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

The real span of all Kronecker products of local Hermitian matrices is the whole Hermitian space on the product index set.

**Theorem 1.7 (A symmetric tensor of two skew directions).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.W_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.W_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

The real matrix J has zero diagonal and off-diagonal entries 1 and −1. Its Kronecker square W is symmetric, since transposition negates both factors.

**Theorem 1.8 (Trace orthogonality).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.blind_spot_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.blind_spot_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

Every Kronecker product of two real symmetric two-by-two matrices has zero trace pairing with W. The pairing factors into local trace pairings with J.

**Theorem 1.9 (Indistinguishable real density matrices).**

Lean statement: `D5/S3/Quantum/Gauge/ComplexLocalTomography.real_density_blind_spot`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ComplexLocalTomography.real_density_blind_spot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. C. Allanach, B. Gripaios, and J. Tooby-Smith (2020). *Solving local anomaly equations in gauge-rank extensions of the Standard Model*. DOI: [10.1103/PhysRevD.101.075015](https://doi.org/10.1103/PhysRevD.101.075015). URL: <https://arxiv.org/abs/1912.10022>.

*Commentary.*

The two matrices I/4 + W/16 and I/4 − W/16 are distinct, strictly positive definite and have trace one. Every product of local real symmetric observables has the same trace pairing with both matrices.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.W_symmetric`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.blind_spot_trace`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.division_algebra_local_tomography_selection`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_complexHermitian`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_quaternionHermitian`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.finrank_realHermitian`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.real_density_blind_spot`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.span_tensor_hermitian`
- Truth anchor: `D5/S3/Quantum/Gauge/ComplexLocalTomography.tensorHermBasis_apply`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
