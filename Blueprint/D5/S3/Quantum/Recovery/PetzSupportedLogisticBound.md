# Supported ordinary Petz recovery with the exact logistic weight

## Abstract

The exact upper-strip evaluation bounds the supported ordinary Petz squared trace error by the entropy loss with coefficient 4(1 + rank T · rank Q).

**Theorem 1.1 (The physical trace error with coefficient four).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSupportedLogisticBound.ordinary_petz_traceNorm_sq_le_entropy_loss`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSupportedLogisticBound.ordinary_petz_traceNorm_sq_le_entropy_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

Take a supported relative modular model for a finite completely positive trace-preserving channel Φ and input density states ρ and σ. In the model R = ρ, T = Φ(ρ), and Q = Φ(σ). The ordinary Petz recovered state is σ¹ᐟ² Φ*(Q⁻¹ᐟ² T Q⁻¹ᐟ²) σ¹ᐟ², with inverse square root on the positive spectrum and zero on the output kernel.

The squared trace norm of R minus this recovered state is at most 4(1 + rank T · rank Q) times the finite trace-log Umegaki loss D(ρ ∥ σ) − D(T ∥ Q). The same channel and pair of states determine both the physical error and the loss.

The completed Stinespring amplitudes have unit Frobenius norm, and the squared norm of their difference is the supported upper-strip deficit. Each coordinate has the constant frequency and at most one frequency for each pair of positive output eigenvalues. Exact logistic evaluation therefore bounds the squared amplitude error at zero by (1 + rank T · rank Q) times the weighted deficit integral. The trace norm of the endpoint Gram difference is at most twice the amplitude error, and the support isometry preserves that trace norm. The strip identity bounds the upper deficit integral by the Umegaki loss.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzSupportedLogisticBound.ordinary_petz_traceNorm_sq_le_entropy_loss`
- Dependency: [D5/S3/Analytic/PetzLogisticEvaluation](../../Analytic/PetzLogisticEvaluation.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSupportedStinespringGram](PetzSupportedStinespringGram.md)
