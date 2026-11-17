# KhetanFiniteRecurrence

## Abstract

Algebraic periodizer bridge for finite-alphabet lattice configurations.

**Theorem 1.1 (A common period for all recurrent lines).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence.directional_recurrence_uniform_period`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence.directional_recurrence_uniform_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A recurrence of order r with nonzero leading coefficient acts at every lattice site. States contain r+1 values from the global finite alphabet. Their deterministic successor gives each line a positive period at most alphabet-size^(r+1); the factorial is one period of the entire configuration. Order zero and zero constant coefficient are included.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence.directional_recurrence_uniform_period`
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanAnnihilator](KhetanAnnihilator.md)
