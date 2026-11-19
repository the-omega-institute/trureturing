# Compact lacunary progression subshifts

## Abstract

Compact lacunary progression subshifts

For m>=3, X_m is the binary two-sided subshift in which no three distinct vertices of any m-term progression of step (m+1)^k can all equal one. Equivalently, every such progression contains at most two ones. The inherited compatible countable-product metric is used throughout.

**Theorem 1.1 (Closed configuration space).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_closed`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each forbidden triple is a finite open cylinder. The intersection of their closed complements is closed in the compact binary product.

**Theorem 1.2 (Integer-translation invariance).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translating a progression only changes its starting coordinate, so every integer shift preserves the exact constraint.

**Theorem 1.3 (Sparse legal points).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_of_subsingleton_support`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_of_subsingleton_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A support of cardinality at most one cannot contain a forbidden triple. The positivity of the progression step separates its distinct vertices.

**Theorem 1.4 (The zero configuration).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_zero_legal`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_zero_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-zero point belongs to every X_m and witnesses nonemptiness.

**Theorem 1.5 (Continuity of the shift).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_shift_continuous`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_shift_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map is the restriction of the genuine full-shift map by one. The closed invariant carrier is compact.

**Theorem 1.6 (Natural-time coordinate formula).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_shift_iterate`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_shift_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The i-fold iterate reads coordinate i+j of the original two-sided configuration. Pseudo-orbit time is natural while symbol coordinates are integers.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_closed`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_of_subsingleton_support`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_legal_shift`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_shift_continuous`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_shift_iterate`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift.lacunary_zero_legal`
- Dependency: [D5/S1/Dynamics/Shadowing/ReturnDistanceShadowing](ReturnDistanceShadowing.md)
