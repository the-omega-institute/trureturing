# Spectral Pairing Capacity Is Monotone under Majorization

## Abstract

Doubly stochastic mixing cannot increase spectral pairing capacity.

**Theorem 1.1 (Doubly stochastic mixing cannot increase spectral pairing capacity).**

$$C_a(r) = \frac{1}{2}\sum_i r_i(a_i - a_{\operatorname{rev} i})\\r = S r' \land \operatorname{DS}(S) \land \operatorname{Antitone}(r') \land \operatorname{Antitone}(a) \Rightarrow C_a(r) \le C_a(r')$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/SpectralPairingCapacity.spectral_pairing_capacity_monotone_of_doubly_stochastic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state spectrum r and observable spectrum a, the spectral pairing capacity is C_a(r) = (1/2) sum_i r_i (a_i - a_{rev i}). Suppose r' and a are nonincreasing and r = S r' for a doubly stochastic matrix S. This is the standard doubly stochastic witness that r is majorized by r'. Then C_a(r) is at most C_a(r').

The observable gap i maps to a_i - a_{rev i}; it is nonincreasing because a is nonincreasing while reversal changes the order. The proof applies the existing bilinear doubly-stochastic inequality to this gap and r'. That inequality is built from the Birkhoff-von Neumann decomposition and mathlib's rearrangement inequality, so those results are reused rather than reproved.

This statement closes only the majorization-monotonicity clause of the source theorem and records its spectral-pairing closed form as a definition. It does not claim the full unitary trace range, the pure-state distance formula, the qubit Bloch-radius reduction, or the source's remaining geometric interpretation.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/SpectralPairingCapacity.spectral_pairing_capacity_monotone_of_doubly_stochastic`
