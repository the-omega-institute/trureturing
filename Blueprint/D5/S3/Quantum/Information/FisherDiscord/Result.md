# Partial trace can increase Fisher discord

## Abstract

A two-qubit flagged state refutes partial-trace monotonicity of Fisher discord.

**Theorem 1.1 (Explicit refutation).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/li-luo-zhang-2025-fisher-discord-partial-trace-refutation` (refuted) by `D5/S3/Quantum/Information/FisherDiscord/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"li-luo-zhang-2025-fisher-discord-partial-trace-refutation","declaration_gid":"D5/S3/Quantum/Information/FisherDiscord/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. Li, S. Luo, Y. Zhang (2025). *Fisher discord as a quantifier of quantum complexity*. DOI: [10.1103/6kv3-hr92](https://doi.org/10.1103/6kv3-hr92). URL: <https://arxiv.org/abs/2510.15375v1>.

*Commentary.*

Use the diagonal qubit state with weights one fifth and four fifths and the Pauli X observable. Its Fisher discord is four twenty-fifths for every Hermitian SLD solution. Explicit Hermitian solutions establish existence on both spaces. The flagged state with support on the basis vectors 00 and 11 has the same marginal and zero discord for the lifted observable, for every Hermitian SLD solution. The classification of diagonal marginals then contradicts the universal partial-trace inequality.

## References

- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Result.result`
- Dependency: [D5/S3/Quantum/Information/FisherDiscord/Extension](Extension.md)
