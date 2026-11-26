# Unitary recovery for a binary random-unitary channel

## Abstract

A unitary decoder maximizes binary random-unitary recovery fidelity.

**Theorem 1.1 (A unitary eigenbasis with unit-modulus diagonal entries).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery.unitary_diagonalize`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery.unitary_diagonalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unitary on Fin d is diagonal in a unitary eigenbasis. The squared modulus of each diagonal entry is one by unitarity.

**Theorem 1.2 (Attainment against all CPTP decoders).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery.binary_unitary_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery.binary_unitary_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vahid Karimipour; Fabio Benatti; Roberto Floreanini (2020). *Quasi-inversion of qubit channels*. DOI: [10.1103/PhysRevA.101.032109](https://doi.org/10.1103/PhysRevA.101.032109). URL: <https://arxiv.org/abs/1909.06118v5>.

*Acknowledgement.* Fereshte Shahbeigi; Koorosh Sadri; Morteza Moradi; Karol Życzkowski; Vahid Karimipour (2021). *Quasi-inversion of quantum and classical channels in finite dimensions*. DOI: [10.1088/1751-8121/ac13db](https://doi.org/10.1088/1751-8121/ac13db). URL: <https://arxiv.org/abs/2104.06062v3>.

*Commentary.*

For each natural d > 0, each pair of real weights p,q ≥ 0 with p+q = 1, and each pair of code unitaries U,V, there exists a unitary Z such that every actual CPTP decoder D has recovery score at most that of the actual CPTP conjugation by Z. Both zero-weight endpoints are included. The objective is the squared canonical entanglement fidelity at I/d in a single use with an untouched reference.

The change of basis uses the relative unitary, with the superscript denoting the complex adjoint.

$$
W = U^{*}V
$$

In a unitary eigenbasis its phases give the diagonal binary channel. The proof transports the weighted Kraus trace expression by left and right unitary factors, then transports an actual optimizing diagonal decoder back to the original basis.

The cited quasi-inversion results provide context for arbitrary qubit channels, orthogonal mixtures in arbitrary dimension, and commuting qutrit mixtures.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery.binary_unitary_optimal`
- Truth anchor: `D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery.unitary_diagonalize`
- Dependency: [D5/S3/Quantum/BlockNorm/EssentiallyHermitian](../BlockNorm/EssentiallyHermitian.md)
- Dependency: [D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel](BinaryRandomUnitaryChannel.md)
