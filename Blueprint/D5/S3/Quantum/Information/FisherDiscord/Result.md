# Fisher discord decreases under a partial trace

## Abstract

A two-qubit flagged state refutes partial-trace monotonicity of Fisher discord.

**Theorem 1.1 (Explicit refutation).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the diagonal qubit state with weights one fifth and four fifths and the Pauli X observable. Its Fisher discord is four twenty-fifths. The flagged state with support on the basis vectors 00 and 11 has the same marginal and zero discord for the lifted observable, so the universal partial-trace inequality fails.

## References

- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Result.result`
- Dependency: [D5/S3/Quantum/Information/FisherDiscord/Extension](Extension.md)
