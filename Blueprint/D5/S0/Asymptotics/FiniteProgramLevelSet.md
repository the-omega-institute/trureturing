# Finite Program Level Sets

## Abstract

Programs over a finite binary alphabet with a bounded description length form a finite level set.

**Theorem 1.1 (Bounded binary programs form a finite level set).**

$$\forall Q\in\mathbb{N}, \operatorname{Finite}(boundedPrograms(Q)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/FiniteProgramLevelSet.bounded_programs_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A binary algorithm program is represented by a list over Fin 2, and boundedPrograms Q selects exactly those lists whose length is at most Q. Mathlib's List.finite_length_le supplies the finite-level-set result, so this declaration is a thin wrapper rather than a re-proof.

This deposit is a partial closure of clause (a) of source theorem 3.4. The body/value non-finiteness clause (b) and the Levin mixed-cost finiteness clause (c) remain unresolved and are intentionally not claimed.

## References

- Truth anchor: `D5/S0/Asymptotics/FiniteProgramLevelSet.bounded_programs_finite`
