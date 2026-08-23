# Bounded Winding Phase Zero Certificate

## Abstract

A finite local zero certificate becomes global under a strict phase bound.

**Theorem 1.1 (A bounded divisible winding phase is zero).**

$$\forall A: \operatorname{PositiveMatrix}, z\in \mathbb{Z}, M\in \mathbb{N},\\{}\operatorname{windingPhase}(A) = z \land \left|z\right| < M \land M \mid z \Rightarrow \operatorname{windingPhase}(A) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/CrossingCertificates/BoundedWindingPhaseZeroCertificate.bounded_winding_phase_zero_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be the repository's canonical positive matrix and let its rational winding phase equal the integer z. The public integrality equation bridges the actual phase carrier to the integer divisibility assertion.

If the absolute value of z is strictly below the natural modulus M and M divides z, the exact integer bounded-divisibility theorem forces z to vanish. Substitution through the public phase equation gives windingPhase(A) = 0.

The proof directly applies the pinned-library theorem Int.eq_zero_of_abs_lt_dvd. Repository searches found and reused PositiveMatrix and windingPhase from the crossing family; no new phase carrier or channel is introduced.

## References

- Truth anchor: `D5/S3/PrimeForms/CrossingCertificates/BoundedWindingPhaseZeroCertificate.bounded_winding_phase_zero_certificate`
- Dependency: [D5/S3/PrimeForms/Crossing/ExactPropagation](../Crossing/ExactPropagation.md)
