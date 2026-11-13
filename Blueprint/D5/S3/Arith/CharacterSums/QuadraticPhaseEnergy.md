# QuadraticPhaseEnergy

## Abstract

Opposite quadratic additive-character phases over an odd finite field have energy equal to the field cardinality.

**Theorem 1.1 (Quadratic phase energy).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticPhaseEnergy.quadratic_phase_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticPhaseEnergy.quadratic_phase_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field of odd characteristic, a nontrivial complex additive character ψ, a nonzero quadratic coefficient d, and any linear coefficient e, the product of the sums of ψ(d x² + e x) and ψ(−(d y² + e y)) equals the field cardinality. The proof expands the product, translates one variable, and applies additive-character orthogonality to the resulting linear sum. This is a reusable bridge between finite-field harmonic analysis and quadratic-phase constructions.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticPhaseEnergy.quadratic_phase_energy`
