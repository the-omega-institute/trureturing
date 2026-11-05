# Schwarz and trace rigidity give actual Petz recovery

## Abstract

Schwarz and trace rigidity give actual Petz recovery.

**Theorem 1.1 (The actual output lies in reference support).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_output_support_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_output_support_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Actual channel support transfer gives P_Q T = T without a full-rank assumption. The statement is used both in Schwarz trace rigidity and to annihilate the complement reset on Phi(rho).

**Theorem 1.2 (One shared Schwarz and trace supplier).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_schwarz_and_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_schwarz_and_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual model let H=sqrt(S), W=Q^(-1/2), Y=W sqrt(T), A=H Psi(Y), C=A P_R, and N=H Psi(W T W) H. The shared supplier proves A A* <= N, C C* <= N, and Tr(N)=Tr(R). The compressed bound follows from the orthogonal input support projection. Both exact recovery from support columns and the quantitative Petz core trace estimate consume these same facts; the Schwarz and trace proof is not duplicated.

**Theorem 1.3 (Positive order plus equal trace forces recovery).**

Lean statement: `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_recovery_of_support_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_recovery_of_support_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

From sqrt(S) Psi(Q^(-1/2) sqrt(T)) P_R = sqrt(R), the actual channel Schwarz inequality yields R <= M M* <= N, where N is the Petz core output. Actual trace pairing and output support give Tr N = Tr R. The positive semidefinite difference of trace zero vanishes, proving N=R. The theorem does not assume recovery or an unproved full-space identity for M.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_recovery_of_support_columns`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_schwarz_and_trace`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_output_support_projection`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](../Divergence/CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](SpectralTransposeRecovery.md)
