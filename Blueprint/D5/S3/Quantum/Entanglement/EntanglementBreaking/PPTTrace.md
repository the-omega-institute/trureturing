# Trace separation for decomposable maps

## Abstract

Output partial transpose and trace separation of decomposable maps.

**Definition 1.1 (Decomposability).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.IsDecomposable`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.IsDecomposable` (`✓ std3`).

*Citation.* Repana Devendra, Nirupama Mallick and K. Sumesh (2023). *Mapping cone of k-entanglement breaking maps*. DOI: [10.1007/s11117-022-00956-4](https://doi.org/10.1007/s11117-022-00956-4). URL: <https://arxiv.org/abs/2105.14991v2>.

*Commentary.*

The positive summand has positive left amplification at every positive integer dimension. The second summand has the same property after transpose on its output. Their sum equals the given complex-linear map.

**Definition 1.2 (Choi matrix from a Hermitian direction).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.choiCandidate`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.choiCandidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a matrix H on the product of two copies of dimension d, the candidate is the identity minus (16/d) times H.

**Definition 1.3 (Trace test from a Hermitian direction).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.pptTest`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.pptTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The test is the unnormalized matrix I + H/(4d).

**Theorem 1.4 (Negative trace pairing excludes decomposability).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.indecomposable_of_ppt_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.indecomposable_of_ppt_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Choi matrix of a decomposable map is the sum of a positive semidefinite matrix and the output partial transpose of another positive semidefinite matrix. Pairing with a positive semidefinite matrix that has positive semidefinite partial transpose is nonnegative.

**Theorem 1.5 (Energy gives a negative trace pairing).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_trace_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tracelessness cancels the terms linear in H. The quadratic contribution is negative and the lower bound on the real trace of H squared forces the unnormalized pairing to be at most minus d squared.

**Theorem 1.6 (Input choi decomposition).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.inputChoi_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.inputChoi_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A decomposition of the map into completely positive and completely copositive parts gives an input-first Choi decomposition P plus the output partial transpose of Q, with P and Q positive semidefinite.

**Theorem 1.7 (Partial transpose trace pairing of psd).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.partialTranspose_trace_pairing_of_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.partialTranspose_trace_pairing_of_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex matrices on a finite product space and a positive semidefinite first matrix Q, move its output partial transpose across the trace pairing with any matrix R.

**Theorem 1.8 (Candidate indecomposable).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_indecomposable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_indecomposable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension d at least one, a traceless H with real trace of H squared at least d to the fourth power over two gives an indecomposable candidate whenever the trace test and its partial transpose are both positive semidefinite.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.IsDecomposable`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_indecomposable`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_trace_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.choiCandidate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.indecomposable_of_ppt_trace`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.inputChoi_decomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.partialTranspose_trace_pairing_of_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.pptTest`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences](ChoiCongruences.md)
- Dependency: [D5/S3/Quantum/Matrix/PartialTransposeTrace](../../Matrix/PartialTransposeTrace.md)
