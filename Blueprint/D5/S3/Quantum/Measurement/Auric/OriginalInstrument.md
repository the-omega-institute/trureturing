# Five-level flagged projective simulation

## Abstract

Exact unhalved diamond error for the five-level flagged AURIC instrument.

**Definition 1.1 (The full input channel with its terminal flag).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.originalInstrument`

*Formalization.* `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.originalInstrument` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two zero-angle Kraus matrices in the source basis are combined with coefficients cos θ and i sin θ. Each Kraus term records its own flag and retains the five-level quantum output.

**Theorem 1.2 (Unitary reduction at each real angle).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.originalInstrument_eq_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.originalInstrument_eq_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unitary on the full input register combines the angle rotation with the change of basis. A unitary on the same output register is selected by the terminal flag. Together these transform the diagonal two-branch target into the actual AURIC instrument on every complex input.

**Theorem 1.3 (Optimal error attained for every real angle).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.original_exact_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.original_exact_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A root of the matching equation on the witness interval gives one common optimal error for all angles. A finite input-independent mixture of projective protocols attains the least uniform amplified trace-norm bound over the diamond closure. The bound tests arbitrary complex inputs with every finite passive reference.

For the lower bound a fixed normalized purification tests the two flag blocks. After a nontrivial first projection, complementary ranks reduce to the rank-one and rank-two estimates. For the upper bound the explicit phase and permutation average of tilted one-measurement protocols has a completely positive Choi majorant. The matching equation gives the same bound as the witness.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.originalInstrument`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.originalInstrument_eq_transport`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/OriginalInstrument.original_exact_distance`
- Dependency: [D5/S3/Quantum/Measurement/Auric/ProtocolLimits](ProtocolLimits.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/UnitaryTransport](UnitaryTransport.md)
