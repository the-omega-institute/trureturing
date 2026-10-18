# S.154 B0 Schur certificate

## Abstract

Exact finite certificates for the registered rank-three B0 recovery probe.

**Theorem 1.1 (The diagonal inverse identities).**

Lean statement: `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_inverse_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_inverse_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed diagonal matrix with entries 6, 8, 56/5, 56/5 and 3 is both a left and a right inverse of the displayed positive diagonal matrix with entries 1/6, 1/8, 5/56, 5/56 and 1/3.

**Theorem 1.2 (The exact Schur interface).**

Lean statement: `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_schur_interface`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_schur_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the fixed real matrices E0, E1 and T, the weighted sum (E0 transpose Y inverse E0 + E1 transpose Y inverse E1)/16 + T transpose Y inverse T/4, with the displayed diagonal inverse, equals the diagonal matrix with entries 1, 1 and 7/50. This is the finite Schur interface used by the rank-three B0 dual certificate.

**Theorem 1.3 (The strict trace slack).**

Lean statement: `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_trace_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational trace value 45/56 is strictly smaller than (1 + 1/square-root of 2)/2.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_inverse_identity`
- Truth anchor: `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_schur_interface`
- Truth anchor: `D5/S3/Quantum/Recovery/S154B0SchurCertificate.b0_trace_bound`
- Dependency: [D5/S3/Quantum/Matrix/SchurMinimum](../Matrix/SchurMinimum.md)
