# Decoherence-Freeze Critical Temperature Criterion

## Abstract

The decoherence-freeze deposit is positive exactly above its critical inverse temperature.

**Definition 1.1 (The freeze deposit subtracts the temperature-scaled entropy tax).**

Lean statement: `D5/S3/QuantumChannels/DecoherenceFreeze.freezeDeposit`

*Formalization.* `D5/S3/QuantumChannels/DecoherenceFreeze.freezeDeposit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For inverse temperature beta, entropy tax Delta S, and passive-energy shift Delta E pass, the freeze deposit is the passive-energy shift minus the entropy tax divided by beta.

**Definition 1.2 (The critical inverse temperature is the entropy-energy ratio).**

Lean statement: `D5/S3/QuantumChannels/DecoherenceFreeze.criticalInverseTemperature`

*Formalization.* `D5/S3/QuantumChannels/DecoherenceFreeze.criticalInverseTemperature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The critical inverse temperature is the entropy tax divided by the passive-energy shift.

**Theorem 1.3 (The freeze deposit is positive exactly above the critical inverse temperature).**

$$0<\beta \land 0<\Delta E_{pass} \Rightarrow (0<\operatorname{freezeDeposit}(\beta,\Delta S,\Delta E_{pass}) \Leftrightarrow \operatorname{criticalInverseTemperature}(\Delta S,\Delta E_{pass})<\beta)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/DecoherenceFreeze.decoherence_freeze_iff_above_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When beta and the passive-energy shift are positive, dividing and cross-multiplying preserve strict inequalities. Consequently, positivity of the freeze deposit is equivalent to beta exceeding the critical entropy-energy ratio.

## References

- Truth anchor: `D5/S3/QuantumChannels/DecoherenceFreeze.criticalInverseTemperature`
- Truth anchor: `D5/S3/QuantumChannels/DecoherenceFreeze.decoherence_freeze_iff_above_critical`
- Truth anchor: `D5/S3/QuantumChannels/DecoherenceFreeze.freezeDeposit`
