# KhetanOneDirectionPeriodizer

## Abstract

Algebraic periodizer bridge for finite-alphabet lattice configurations.

**Theorem 1.1 (From a line annihilator to a global period).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero polynomial annihilator in a nonzero lattice direction yields a nonzero period of the original finite-range configuration. No periodic-line conclusion or nonzero constant coefficient is assumed. This is the terminal recurrence step, not the complete one-direction periodizer theorem.

**Theorem 1.2 (Separate parallel and transverse difference factors).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.integer_periodizer_direction_split`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.integer_periodizer_direction_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a primitive lattice direction, its integer Bezout coordinates express every parallel supplier direction as an integer multiple. Grouping all such factors gives a nonzero one-variable Laurent factor A and retains every transverse factor in B, with AB annihilating the original integer configuration after coefficient transport to any domain. In particular the complex coefficient action uses exactly the image of that original configuration. Parallel or repeated transverse factors remain permitted.

**Theorem 1.3 (Obtain a global period from the cleared identity).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.cleared_bezout_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.cleared_bezout_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero lattice direction u, let P act as a constant on the given finite-range configuration, and let lineLaurent u A times B annihilate it. A cleared Laurent identity with nonzero one-variable coefficient rho and nonzero A makes (z-1) A rho a nonzero line annihilator, so the recurrence theorem gives a global period of that same configuration. KhetanDirectionalCoprimality.one_direction_periodic supplies the identity using transverse_product_coprime and KhetanLaurentElimination.clear_laurent_bezout. Rational functions do not act on the configuration.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.cleared_bezout_periodic`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.integer_periodizer_direction_split`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic`
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanAnnihilator](KhetanAnnihilator.md)
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence](KhetanFiniteRecurrence.md)
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanLaurentElimination](KhetanLaurentElimination.md)
