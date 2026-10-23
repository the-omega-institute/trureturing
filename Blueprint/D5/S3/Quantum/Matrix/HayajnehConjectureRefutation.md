# A counterexample to mixed-power norm monotonicity

## Abstract

Two positive definite rational matrices reverse the trace-norm comparison at powers one half and three quarters, refuting the proposed monotonicity for all unitarily invariant norms.

**Definition 1.1 (Conjecture 1 for every unitarily invariant norm).**

Lean statement: `D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.conjecture`

*Formalization.* `D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.conjecture` (`✓ std3`).

*Citation.* Mostafa Hayajneh; Saja Hayajneh; Fuad Kittaneh (2018). *On some classical trace inequalities and a new Hilbert–Schmidt norm inequality*. DOI: [10.7153/mia-2018-21-81](https://doi.org/10.7153/mia-2018-21-81). URL: <https://doi.org/10.7153/mia-2018-21-81>.

*Commentary.*

Let A be a positive semidefinite matrix and B be a Hermitian matrix. Then for 1/2 ≤ s ≤ t ≤ 1 and for every unitarily invariant norm, the proposed inequality is N(A^s B + B A^(1−s)) ≤ N(A^t B + B A^(1−t)).

The formal proposition quantifies over every natural dimension n, all complex n by n matrices A and B, the positive semidefinite condition on A, the Hermitian condition on B, every real pair s,t in the displayed order, and every unitarily invariant norm on that matrix space. Matrix powers use continuous functional calculus on the positive semidefinite input. No additional lower spectral bound is imposed on A.

**Theorem 1.2 (Conjecture 1 is false).**

Lean statement: `D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hayajneh-2018-unitarily-invariant-norm` (refuted) by `D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hayajneh-2018-unitarily-invariant-norm","declaration_gid":"D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mostafa Hayajneh; Saja Hayajneh; Fuad Kittaneh (2018). *On some classical trace inequalities and a new Hilbert–Schmidt norm inequality*. DOI: [10.7153/mia-2018-21-81](https://doi.org/10.7153/mia-2018-21-81). URL: <https://doi.org/10.7153/mia-2018-21-81>.

*Commentary.*

Take n=2, A=diag(1/81,1), B=[[1,3/4],[3/4,1]], s=1/2 and t=3/4. Both matrices are positive definite, and B is Hermitian. Diagonal functional calculus gives A^(1/2)=diag(1/9,1), A^(1/4)=diag(1/3,1) and A^(3/4)=diag(1/27,1). Thus L=A^(1/2)B+BA^(1/2)=[[2/9,5/6],[5/6,2]] and R=A^(3/4)B+BA^(1/4)=[[10/27,7/9],[1,2]].

The trace norm is an instance of the unitarily invariant norm interface. For every complex two by two matrix T, its square is tr(T* T)+2|det T|: the squared singular values sum to tr(T* T), and the product of the singular values is |det T|. This identity also applies to the non-Hermitian matrix R. Here det L=−1/4, det R=−1/27, the squared trace norm of L is 481/81, and that of R is 4240/729. Their difference is 89/729>0.

Nonnegativity of both norms therefore gives N(L)>N(R) for the trace norm, contradicting the conjecture. The sum of both singular values is the full prefix in dimension two, so the same comparison obstructs weak majorization at that prefix. The known Hilbert–Schmidt case and the endpoint s=1/2,t=1 remain valid. This refutation does not decide the universal restrictions to Schatten exponents at least two or to the operator norm.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.conjecture`
- Truth anchor: `D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](SpectralPower.md)
- Dependency: [D5/S3/Quantum/Schatten/TraceNorm](../Schatten/TraceNorm.md)
