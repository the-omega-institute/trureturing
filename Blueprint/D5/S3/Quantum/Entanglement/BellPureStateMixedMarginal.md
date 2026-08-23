# A Pure Bell State with a Mixed Marginal

## Abstract

The pure Bell density has the maximally mixed one-qubit marginal.

**Theorem 1.1 (The Bell pure state reduces to one half of the identity).**

$$\begin{gathered}\langle\operatorname{bellVector}\mid\operatorname{bellVector}\rangle = 1 \land\\{}\operatorname{bellDensity} \geq 0 \land\\{}\operatorname{Tr}(\operatorname{bellDensity}) = 1 \land\\{}\operatorname{rank}(\operatorname{bellDensity}) = 1 \land\\{}\operatorname{bellDensity}^{2} = \operatorname{bellDensity} \land\\{}\operatorname{traceEnvironment}(\operatorname{bellDensity}) = \frac{1}{2} I \land\\{}\operatorname{traceEnvironment}(\operatorname{bellDensity})^{2} \neq \operatorname{traceEnvironment}(\operatorname{bellDensity}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal.bell_pure_state_has_maximally_mixed_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The amplitude is the canonical normalized Bell vector obtained from the standard coefficients for the two computational-basis terms. Its outer product is the canonical Bell density matrix.

Normalization, positivity, trace one, rank one, and idempotence are all public clauses. Together they certify that the joint two-qubit density is pure rather than merely naming it as a pure state.

The partial trace is constructed by summing the equal environment indices. It is exactly one half of the qubit identity, and its failure of idempotence is public evidence that the marginal is mixed.

The proof applies the existing rank-one handshake and Bell-state certificate, then evaluates the four finite matrix entries. No repository theorem already packaged the Bell partial trace.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal.bell_pure_state_has_maximally_mixed_marginal`
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
