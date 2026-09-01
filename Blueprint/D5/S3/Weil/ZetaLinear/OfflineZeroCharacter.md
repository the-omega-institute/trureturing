# Offline-Zero Nonunitary Characters

## Abstract

Offline-zero parameters define continuous log-scale Mellin characters, with real part measuring the obstruction to unitarity.

**Definition 1.1 (The log-scale character of an offline zero).**

Lean statement: `D5/S3/Weil/ZetaLinear/OfflineZeroCharacter.offlineZeroCharacter`

*Formalization.* `D5/S3/Weil/ZetaLinear/OfflineZeroCharacter.offlineZeroCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex zero parameter rho, the definition realizes the continuous character t maps to exp((rho - 1/2)t) from the additive real line, represented multiplicatively, to the complex numbers.

The accompanying Lean theorems split this value as exp(delta t) times exp(i gamma t), identify unitarity with delta equal to zero, and prove the parameter sequence from the imaginary axis through the complex plane to the real-part obstruction is short exact.

The definition is not empty or vacuous: exists_nonunitary_offline_zero_character constructs rho equal to one and proves that its character is genuinely nonunitary.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/OfflineZeroCharacter.offlineZeroCharacter`
- Dependency: [D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening](ReflectedZeroModePhaseFlattening.md)
