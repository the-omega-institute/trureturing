# KhetanLaurentElimination

## Abstract

Algebraic periodizer bridge for finite-alphabet lattice configurations.

**Theorem 1.1 (Clear a Laurent Bezout identity).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fraction-field Laurent Bezout identity is multiplied by nonzero common denominators. The resulting constant is proved nonzero in the coefficient domain, with both multipliers in the original Laurent ring. Localized coprimality is an explicit intermediate premise; its derivation from the line-factor restriction is not established here.

**Theorem 1.2 (Produce the identity from monic transverse factors).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout_of_monic_factors`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout_of_monic_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For monic factors, divisibility in the coefficient fraction field descends by polynomial division. Multiplication by a Laurent monomial only changes the dividend by a unit. If each mapped factor is irreducible and its Laurent image does not divide P, polynomial Bezout identities give coprimality with their product and with B. Clearing denominators then gives a nonzero coefficient in the original domain. Identifying these factors with the transverse lattice binomials is a separate obligation.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout_of_monic_factors`
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanAnnihilator](KhetanAnnihilator.md)
