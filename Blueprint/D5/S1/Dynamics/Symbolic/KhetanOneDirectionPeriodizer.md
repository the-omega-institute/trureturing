# KhetanOneDirectionPeriodizer

## Abstract

Algebraic periodizer bridge for finite-alphabet lattice configurations.

**Theorem 1.1 (Exact-cover annihilator of the original configuration).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.exact_cover_product_differences`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.exact_cover_product_differences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive-shift operators use the negative-exponent tile mask. Exact coverage makes that mask act as the constant one configuration. A lattice difference supplies a nonzero annihilator, and the pinned product-difference supplier acts directly on the original integer configuration.

**Theorem 1.2 (From a line annihilator to a global period).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero polynomial annihilator in a nonzero lattice direction yields a nonzero period of the original finite-range configuration. No periodic-line conclusion or nonzero constant coefficient is assumed. This is the terminal recurrence step, not the complete one-direction periodizer theorem.

**Theorem 1.3 (Separate parallel and transverse difference factors).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.integer_periodizer_direction_split`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.integer_periodizer_direction_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a primitive lattice direction, its integer Bezout coordinates express every parallel supplier direction as an integer multiple. Grouping all such factors gives a nonzero one-variable Laurent factor A and retains every transverse factor in B, with AB annihilating the original integer configuration after coefficient transport to any domain. In particular the complex coefficient action uses exactly the image of that original configuration. Parallel or repeated transverse factors remain permitted.

**Theorem 1.4 (Use a cleared identity before acting on the configuration).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.localized_bezout_step`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.localized_bezout_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitivity constructs integral lattice Laurent coordinates, with the chosen direction in the coefficient ring. A finite monic factorization of B, whose factors remain irreducible over the coefficient fraction field and do not divide P in the original Laurent ring, proves localized coprimality. Denominator clearing constructs a nonzero horizontal coefficient rho. The resulting polynomial (z-1) A rho annihilates the original configuration, whose finite range gives a global period. No coprimality or nonzero eliminant is assumed in this step. Constructing the monic factors and proving their irreducibility and nondivisibility from the line-factor restriction, and hence the complete one-direction periodizer theorem, remain unproved.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.exact_cover_product_differences`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.integer_periodizer_direction_split`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.localized_bezout_step`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic`
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanAnnihilator](KhetanAnnihilator.md)
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence](KhetanFiniteRecurrence.md)
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanLaurentElimination](KhetanLaurentElimination.md)
