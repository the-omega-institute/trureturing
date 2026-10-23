# Mechanical Dyadic Boundary

## Abstract

Upper dyadic slopes eventually preserve every fixed finite mechanical observation.

**Theorem 1.1 (Upper approximation preserves a finite observation).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real slope, phase, and finite word length, all sufficiently precise upper dyadic approximations have the same actual mechanical bits throughout that word. The precision threshold may depend on the slope, phase, and word length, including at integer-hit phases. For the contrasting lower approximants, let alpha be irrational and strictly between zero and one, beta_p = floor(2^p*alpha)/2^p for every natural precision p, and x = 1-alpha. The floor bound and irrationality give 0 <= beta_p < alpha. Hence x is in (0,1), x+alpha = 1, and 0 < x+beta_p < 1. The cumulative floors at x are zero for both slopes; the next floor is one at alpha and zero at beta_p. Thus the actual first mechanical letter is one at alpha and zero at every lower approximant, and the corresponding Boolean bits disagree for every p. Increasing parameter precision therefore does not guarantee equality of the bit at this exact boundary. This is a direct application of the existing floor and mechanical-word definitions, not an additional theorem or a uniform failure away from integer hits.

**Theorem 1.2 (Finite words away from integer hits).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.finite_word_stable_off_integer_hits`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.finite_word_stable_off_integer_hits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When no positive-time cumulative floor in a fixed finite prefix lands on an integer, one positive slope radius preserves every cumulative floor and every actual mechanical bit in that prefix. The radius is constructed from the finite set of distances to neighboring integers.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.dyadic_upper_eventually_word_eq`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDyadicBoundary.finite_word_stable_off_integer_hits`
- Dependency: [D5/S1/Words/Mechanical/MechanicalSlopeSensitivity](MechanicalSlopeSensitivity.md)
