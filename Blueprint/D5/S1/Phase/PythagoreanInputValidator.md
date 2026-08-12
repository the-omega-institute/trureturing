# Pythagorean Input Validator

## Abstract

A decidable integer gate accepts a genuine pin input and rejects a one-coordinate perturbation.

**Theorem 1.1 (Boolean acceptance is equivalent to the Eisenstein equation).**

$$\forall x: \operatorname{PinInput},\ x.accepts = true \Leftrightarrow x.beta^{2} - x.beta * x.\gamma_{0} + x.\gamma_{0}^{2} = x.m * (x.m + 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/PythagoreanInputValidator.accepts_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every PinInput record, the executable Boolean gate returns true exactly when the normalized Eisenstein equation holds for its three fields. The proof reduces Boolean decision to the proposition and then reuses the existing Pythagorean-gate normalization theorem.

This validator checks only the displayed Diophantine equation. It makes no claim about primitivity, orbit provenance, or any stronger admissibility condition.

**Theorem 1.2 (A genuine input is accepted and its beta perturbation is rejected).**

$$PinInput.accepts(\{beta : = -384, \gamma_{0} : = 138, m : = 468\}) = true \land PinInput.accepts(\{beta : = -383, \gamma_{0} : = 138, m : = 468\}) = false$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/PythagoreanInputValidator.genuine_and_perturbed_input_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source-attested PinInput record with beta minus 384, gamma-zero 138, and m 468 passes the gate. Changing only its beta field to minus 383 fails it. These opposite Boolean outcomes ensure that acceptance depends on the supplied input and is not a constant or vacuous predicate.

## References

- Truth anchor: `D5/S1/Phase/PythagoreanInputValidator.accepts_iff`
- Truth anchor: `D5/S1/Phase/PythagoreanInputValidator.genuine_and_perturbed_input_certificate`
- Dependency: [D5/S1/Phase/SeatTowerArithmetic](SeatTowerArithmetic.md)
