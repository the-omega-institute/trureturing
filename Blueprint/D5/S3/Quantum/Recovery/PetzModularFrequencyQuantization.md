# Retained modular frequency quantization for ordinary Petz recovery

## Abstract

The ordinary Petz squared trace error is controlled by the number of retained frequency centres and the exact logistic cost of the assignment.

**Theorem 1.1 (Exact logistic discrepancy on the retained spectral law).**

Lean statement: `D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.exact_phase_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.exact_phase_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

Let T = Φ(ρ) and Q = Φ(σ) be the actual retained states of a finite CPTP channel. For positive eigenvalues pₖ and qₗ, the spectral pair has frequency log pₖ − log qₗ and mass pₖ times the squared overlap of the corresponding eigenvectors. The finite sum combines the masses of coincident frequencies and agrees with the spectral-projection formula for repeated eigenvalues.

An assignment ψ changes only the retained phase of each spectral pair. The exact weighted squared Frobenius discrepancy between the original and assigned completed Stinespring amplitudes equals J, the mass-weighted sum of 2(1 − κ(ω − ψ(ω))). Here κ(0) = 1 and κ(x) = (x/2)/sinh(x/2) away from zero.

The completed Stinespring columns form a coisometry. Trace pairing with the actual channel then weights the retained factor by Q. In the positive spectral columns, orthogonality removes cross terms and Q cancels the inverse square-root weights.

**Theorem 1.2 (Physical ordinary Petz recovery with finitely many centres).**

Lean statement: `D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.ordinary_petz_traceNorm_sq_le_quantized_phase_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.ordinary_petz_traceNorm_sq_le_quantized_phase_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

Take the supported relative modular model of the actual channel and density states with supp ρ contained in supp σ. Assign every positive-mass retained frequency to a finite set of m real centres. The squared trace norm of ρ minus its ordinary Petz recovery is at most 4(m + 1)(√Δ + √J)², where Δ is the channel's finite trace-log Umegaki loss.

The inverse square root acts on the positive spectrum of Q and vanishes on its kernel. The bound applies to singular retained states and uses no positive spectral lower bound. Zero-mass pairs have zero amplitude coefficients and impose no restriction on the assignment.

Every assigned phase equals one at zero, so the assigned amplitude has the same zero-phase Gram and ordinary Petz endpoint. The weighted L² triangle inequality combines the actual strip deficit with the exact discrepancy. Coordinatewise logistic evaluation counts the shifted centres and the constant term, and the physical Gram inequality contributes the factor four.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.exact_phase_discrepancy`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.ordinary_petz_traceNorm_sq_le_quantized_phase_cost`
- Dependency: [D5/S3/Quantum/Recovery/PetzSupportedLogisticBound](PetzSupportedLogisticBound.md)
