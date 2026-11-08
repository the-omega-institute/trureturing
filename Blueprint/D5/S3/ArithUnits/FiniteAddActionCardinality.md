# Finite Additive Actions and Support Cardinality

## Abstract

Finite additive actions turn invariant supports into divisibility statements.

**Theorem 1.1 (A pretransitive invariant support is empty or full).**

Lean statement: `D5/S3/ArithUnits/FiniteAddActionCardinality.invariant_finset_empty_or_univ_of_pretransitive`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/FiniteAddActionCardinality.invariant_finset_empty_or_univ_of_pretransitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite type carrying a pretransitive additive group action, a Finset whose image is unchanged by every group element is either empty or the whole state space. The proof transports one chosen support point to an arbitrary target, so the conclusion is an orbit statement rather than a pointwise accident.

**Theorem 1.2 (A free finite action forces group-order divisibility).**

Lean statement: `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_free_finite_action`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_free_finite_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite additive groups and finite state spaces, freeness makes every nonempty orbit have the same size as the acting group. Burnside's fixed point sum therefore yields that the acting group cardinality divides the state-space cardinality. This records the arithmetic content of orbit decomposition directly in Lean.

**Theorem 1.3 (A free invariant support inherits group-order divisibility).**

Lean statement: `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_invariant_finset_of_free_action`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_invariant_finset_of_free_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a finite support is invariant under a free additive action, the action restricts to its subtype. Applying the orbit count there proves that the group cardinality divides the support cardinality. In the affine commutator setting, a nonzero prime-field translation supplies exactly this free action, turning the commutator into a numerical obstruction on the support.

**Theorem 1.4 (A free invariant relation inherits group-order divisibility).**

Lean statement: `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_invariant_relation_of_free_action`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_invariant_relation_of_free_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite relation on X × X carries the diagonal additive action. If the relation is invariant and the action on X is free, the diagonal action is free because a fixed pair would give a fixed first coordinate. The orbit count therefore forces the group cardinality to divide the number of ordered pairs in the relation. This applies directly to invariant directed graphs and pair constraints.

## References

- Truth anchor: `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_free_finite_action`
- Truth anchor: `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_invariant_finset_of_free_action`
- Truth anchor: `D5/S3/ArithUnits/FiniteAddActionCardinality.card_addGroup_dvd_of_invariant_relation_of_free_action`
- Truth anchor: `D5/S3/ArithUnits/FiniteAddActionCardinality.invariant_finset_empty_or_univ_of_pretransitive`
