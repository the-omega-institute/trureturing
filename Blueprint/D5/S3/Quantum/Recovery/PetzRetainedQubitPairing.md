# Ordinary Petz recovery at retained qubit rank

## Abstract

The ordinary Petz channel has squared trace error at most (8 + 2√2) times the Umegaki loss at retained support rank at most two.

**Definition 1.1 (Logistic Fourier correlation).**

Lean statement: `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.logisticCorrelation`

*Formalization.* `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.logisticCorrelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fourier correlation of the upper strip weight is K(t) = (t/2)/sinh(t/2), with K(0) = 1.

**Theorem 1.2 (Ordinary Petz error with retained support rank at most two).**

Lean statement: `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_gaps`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_gaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For every finite CPTP channel and reference state, the ordinary Petz channel recovers the reference exactly. Its action uses the actual Kraus adjoint, the inverse square root on the positive output spectrum and the reference-state replacement on the complementary support.

For each supported source, let Δ be the finite trace-log Umegaki entropy loss. If the reference output has rank at most two and the source output has rank at most one, the squared full trace norm error is bounded by 8Δ. If the reference output has rank at most two, the source output has rank two, and both positive output log-eigenvalue differences have K at most 1/5, the squared error is at most (8 + 2√2)Δ.

The mixed source and reference eigenbases give opposite blocks with equal unitary-entry moduli. Hermiticity of the physical square roots ties the off-diagonal amplitudes to their adjoints. The centered logistic determinant controls both blocks at once, and the Stinespring strip comparison and Gram endpoint transfer the bound to the ordinary recovered state.

**Theorem 1.3 (Ordinary Petz bound for all retained qubit spectra).**

Lean statement: `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_output`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For every finite CPTP channel and reference density state, the ordinary Petz channel uses the actual Kraus adjoint, the inverse square root on the positive reference output spectrum and the reference-state replacement on its complementary support. It recovers the reference exactly. When the reference output has rank at most two, the squared full trace norm error on every supported input is at most (8 + 2√2)Δ, where Δ is the finite trace-log Umegaki loss.

For two rank-two outputs, each scalar entry of a mixed spectral block has three frequency slots, the central slot and the two marginal gaps. When either marginal correlation reaches one fifth, the logistic Gram is realized by three rank-one projectors even when frequencies coincide. The identity represents the coefficient sum. Projecting it away from a Hermitian matrix orthogonal to all three projectors gives a squared evaluation norm at most 8/3. Summing the scalar estimates gives the same factor in every finite environment dimension.

The centered estimate covers separated spectra and the linear level count covers source output rank at most one. The supported strip and Gram inequalities pass these bounds to the ordinary recovered state, including singular states on their supports.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.logisticCorrelation`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_gaps`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_output`
- Dependency: [D5/S3/Quantum/Recovery/PetzSupportedLinearRank](PetzSupportedLinearRank.md)
