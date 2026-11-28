# Sharp half power for coherent erasure

## Abstract

Three physical flags give the exact Bures square of the ordinary Petz outputs.

Dephase the environment of the coherent reference. Compute the ordinary Petz output from the dephased reference and also transport the original output by the same three-flag channel.

**Theorem 1.1 (Physical dephasing channel).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.dephase_is_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.dephase_is_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three orthogonal flag projectors are Kraus operators of the dephasing channel.

**Theorem 1.2 (Positive root of the coherent reference).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.sqrt_sigma`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.sqrt_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coherent rank-one part and the third-flag part have orthogonal supports.

**Theorem 1.3 (Positive root of the dephased reference).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.sqrt_dephase_sigma`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.sqrt_dephase_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix square root is the block diagonal of the three positive qubit roots.

**Theorem 1.4 (Three blocks of the transported ordinary Petz output).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y0_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y0_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With p = ε/(1 + ε) and 0 < ε < 1, the first two conditional projectors have weight p/2 each. The third block is M/4.

**Theorem 1.5 (Three blocks of the recomputed ordinary Petz output).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y1_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y1_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first block is zero, the second conditional projector has weight p, and the third block is M/4.

**Theorem 1.6 (Both benchmarks are density matrices).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y0_Y1_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y0_Y1_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks are positive semidefinite and their weights sum to one for each output.

**Theorem 1.7 (Exact paired defect).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Gamma_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Gamma_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairing the matrix difference with the lifted retained likelihood gives Γ = 2p².

**Theorem 1.8 (Exact quantum root fidelity).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.rootFidelity_Y0_Y1`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.rootFidelity_Y0_Y1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positive matrix roots in the fidelity formula give contributions 0, p/√2, and 1 − p from the three flags.

**Theorem 1.9 (Exact squared Bures distance).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.bures_sq_Y0_Y1`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.bures_sq_Y0_Y1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace-one Bures convention gives d_B² = 2p(1 − 1/√2).

**Theorem 1.10 (Equality at the half power).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.bures_sq_eq_sqrt_Gamma`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.bures_sq_eq_sqrt_Gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity d_B² = (√2 − 1)√Γ holds throughout the family. As ε tends to zero, Γ tends to zero and the positive ratio stays fixed.

**Theorem 1.11 (Optimal one-copy label test).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.one_copy_label_test_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.one_copy_label_test_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Guess the transported benchmark exactly on the first flag. The equal-prior error is (1 − p/2)/2 and is minimal over binary effects.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Gamma_eq`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y0_Y1_density`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y0_eq`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.Y1_eq`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.bures_sq_Y0_Y1`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.bures_sq_eq_sqrt_Gamma`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.dephase_is_channel`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.one_copy_label_test_optimal`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.rootFidelity_Y0_Y1`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.sqrt_dephase_sigma`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzCoherentErasureSharpPower.sqrt_sigma`
- Dependency: [D5/S3/Quantum/CommutingMidpoint/Fidelity](../../CommutingMidpoint/Fidelity.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinementPetz](../BKMFlagRefinementPetz.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../SpectralTransposeRecovery.md)
