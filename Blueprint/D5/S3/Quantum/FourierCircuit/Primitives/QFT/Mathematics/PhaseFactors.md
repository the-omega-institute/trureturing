# Primitives QFT Mathematics PhaseFactors

## Abstract

Addressed quantum circuit: Primitives QFT Mathematics PhaseFactors

**Definition 1.1 (qftPhaseAngle).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Rotation angle used between the leading wire and the (offset+1)st wire of one recursive QFT stage.

**Definition 1.2 (qftPhaseLayerFactorPrefix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Scalar accumulated by the first count controlled phases of one QFT stage on a computational-basis label.

**Definition 1.3 (qftPhaseFactorAt).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One phase-layer factor, indexed in source-circuit order.

**Lemma 1.4 (natOfBits eq sum).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.natOfBits_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.natOfBits_eq_sum` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reconstruct a natural number as the weighted sum of its finite bit vector.

**Lemma 1.5 (qftPhaseLayerFactorPrefix eq prod).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix_eq_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix_eq_prod` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The recursive scalar accumulator is exactly the product of the phase factors represented by its first count structural leaves.

**Lemma 1.6 (qftPhaseAngle exp eq omega pow).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle_exp_eq_omega_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle_exp_eq_omega_pow` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The source angle of one phase leaf is the corresponding binary-weight power of the common (n+1)-qubit Fourier root.

**Lemma 1.7 (qftPhaseFactorAt eq omega pow).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt_eq_omega_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt_eq_omega_pow` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Each actual controlled-phase leaf contributes the Fourier-root power of its addressed input bit, and contributes one when the leading bit is zero.

**Lemma 1.8 (qftPhaseLayerFactor eq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactor_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactor_eq` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The complete phase layer contributes the Fourier root raised to the lower n input bits whenever the leading output branch is one.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.natOfBits_eq_sum`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle_exp_eq_omega_pow`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt_eq_omega_pow`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix_eq_prod`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactor_eq`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Operator](../../../Components/Gates/ControlledPhase/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics](../Mathematics.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow](../../../Util/FinPow.md)
