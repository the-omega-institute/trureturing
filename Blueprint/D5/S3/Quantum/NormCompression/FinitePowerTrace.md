# Finite two-row trace power

## Abstract

Actual finite two-row trace powers on the full nonnegative cone.

**Definition 1.1 (Actual operator trace power).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq`

*Formalization.* `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite column type m, Aq q W is the complex embedding of the real entrywise roots W^(1/(2q)), and Fq q W is schattenPow (2q) (Aq q W). On entrywise nonnegative tables this is the actual Schatten power, with no rank or invertibility restriction.

**Theorem 1.2 (Row Gram operator power).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq_eq_trace_rpow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq_eq_trace_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real q > 0, Fq q W equals the real part of the trace of the actual CFC q-th power of Aq q W times its adjoint. The finite column type may be empty.

**Theorem 1.3 (Continuity including zero entries).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerTrace.continuous_Fq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerTrace.continuous_Fq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real q > 0 and every finite column type, Fq q is continuous on the entire real matrix space. Restriction therefore gives continuity on the full nonnegative cone, including singular Gram matrices and all axial tables.

**Theorem 1.4 (Nonnegative degree-one homogeneity).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real q > 0, c >= 0 and entrywise nonnegative W, Fq q (c times W) = c times Fq q W. The zero scalar and zero table are included.

**Theorem 1.5 (Actual radial second derivative).**

Lean statement: `D5/S3/Quantum/NormCompression/FinitePowerTrace.radial_second_derivative_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/NormCompression/FinitePowerTrace.radial_second_derivative_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q > 0, real c and nonnegative W, the actual second derivative at t = 0 of Fq q ((1 + tc) times W) is zero. This proves the radial inclusion only; it does not assert a converse kernel classification.

The full-cone concavity theorem for 1 < q < 2, its exact support-restricted strict kernel and the local-output-orthogonal compression budget are proved in their separate owning modules. Empty finite column types are included in all universal statements; their singular-value sum is zero. Fixed-congruence Carlen-Lieb convexity on positive definite matrices is not used as a substitute for these statements.

## References

- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq_eq_trace_rpow`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerTrace.Fq_smul`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerTrace.continuous_Fq`
- Truth anchor: `D5/S3/Quantum/NormCompression/FinitePowerTrace.radial_second_derivative_zero`
- Dependency: [D5/S3/Quantum/NormCompression/SchattenContinuity](SchattenContinuity.md)
