# Iterative Petz recovery under single-axis dephasing

## Abstract

Exact phase-aligned qubit update and the asymptotic bias of iterative Petz recovery.

**Theorem 1.1 (Petz update in the phase-aligned qubit slice).**

Lean statement: `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing.matrixStep_eq_principal_petz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing.matrixStep_eq_principal_petz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lea Lautenbacher, Felix Ahnefeld, Susana F. Huelga, and Martin B. Plenio (2026). *Iterative Petz Protocols for Quantum State Recovery*. DOI: [10.48550/arXiv.2611.32995](https://doi.org/10.48550/arXiv.2611.32995). URL: <https://arxiv.org/abs/2611.32995v1>.

*Commentary.*

The explicit real matrix update uses the principal square root of the reference and the inverse principal square root of its dephased image. The off-diagonal and diagonal entries yield the two coordinate updates.

**Theorem 1.2 (Pure limit with a strict axial fidelity deficit).**

Lean statement: `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing.pure_target_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing.pure_target_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lea Lautenbacher, Felix Ahnefeld, Susana F. Huelga, and Martin B. Plenio (2026). *Iterative Petz Protocols for Quantum State Recovery*. DOI: [10.48550/arXiv.2611.32995](https://doi.org/10.48550/arXiv.2611.32995). URL: <https://arxiv.org/abs/2611.32995v1>.

*Commentary.*

For a coherence multiplier strictly between zero and one, the orbit from the unbiased first recovery converges to the unit Bloch circle. At nonzero latitude the strict loss in absolute axial component at the second recovery gives a persistent fidelity deficit. An equatorial target is recovered in the limit.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing.matrixStep_eq_principal_petz`
- Truth anchor: `D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing.pure_target_limit`
