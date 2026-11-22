# Ordinary Petz recovery with a linear rank bound

## Abstract

The ordinary Petz squared trace error is bounded by the actual Umegaki loss with coefficient 4(ν₊(T) + ν₊(Q) − 1).

**Definition 1.1 (Distinct positive eigenvalues).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedLinearRank.positiveLevelCount`

*Formalization.* `D5/S3/Quantum/Recovery/PetzSupportedLinearRank.positiveLevelCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the eigenvalues of the density matrix on their positive spectral indices and count the elements of the image.

**Theorem 1.2 (The finite CPTP ordinary Petz bound).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedLinearRank.ordinary_petz_traceNorm_sq_le_four_linear_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedLinearRank.ordinary_petz_traceNorm_sq_le_four_linear_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

For every finite CPTP channel Φ and reference density state σ, let Q = Φ(σ) and P be its support projection. The theorem gives the ordinary Petz channel with the actual Kraus adjoint and the inverse square root of Q on its positive spectrum. Its extension on the kernel adds Tr((I − P)X) σ to the action on X. It recovers σ exactly. For every ρ supported in σ, that extension contributes zero at T = Φ(ρ). The squared trace norm of ρ minus the recovered T is at most 4(ν₊(T) + ν₊(Q) − 1) Δ and at most 4(2 rank Q − 1) Δ, where Δ = D(ρ ∥ σ) − D(T ∥ Q) uses the actual finite trace-log relative entropies and ν₊ counts distinct positive eigenvalues.

The actual Stinespring amplitudes realize both supported strip deficits. Their reflected cross term survives the input support projections. The midline identity gives the full logistic energy bound, the mixed eigenbasis gives the distinct-level coefficient, and the endpoint Gram is the ordinary recovered state.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedLinearRank.ordinary_petz_traceNorm_sq_le_four_linear_rank`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedLinearRank.positiveLevelCount`
- Dependency: [D5/S3/Analytic/PetzLogisticMatrixStrip](../../Analytic/PetzLogisticMatrixStrip.md)
- Dependency: [D5/S3/Quantum/Recovery/CanonicalPetzEquality](CanonicalPetzEquality.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation](PetzMixedBoundaryEvaluation.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSupportedStinespringGram](PetzSupportedStinespringGram.md)
