# Forced Fourier zeros

## Abstract

Finite frequency support of low even powers.

**Theorem 1.1 (Modes beyond the even power support).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_even_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_even_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural s,j,m with s less than j and j at most m, the real Fourier mode at exponent 2s vanishes. A finite cosine sum gives the initial constant-power case. Multiplication by the squared cosine shifts a frequency by at most one; induction preserves vanishing beyond the support. The argument includes s=0 and does not require the odd order to be prime.

**Theorem 1.2 (Simultaneous zeros of mode differences).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_gap_even_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_gap_even_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural step d, if s is less than j and j+d is at most m, the difference of modes j and j+d vanishes at exponent 2s. Both modes lie beyond the same finite frequency support. The steps one and two used for spectral separation are included.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_even_eq_zero`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros.modeValue_gap_even_eq_zero`
- Dependency: [D5/S3/Quantum/Matrix/JainAbsCosine/Defs](Defs.md)
