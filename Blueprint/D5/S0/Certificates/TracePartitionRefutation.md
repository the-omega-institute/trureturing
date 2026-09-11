# Trace Partition Refutation

## Abstract

Congruence and complete reuse-or-fresh branching refute the existing bounded FitsTrace problem, with exact recurrent and signature costs.

**Definition 1.1 (Respects).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.Respects`

*Formalization.* `D5/S0/Certificates/TracePartitionRefutation.Respects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Branch equalities constrain the actual trace colors.

**Definition 1.2 (Equality).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.Equality`

*Formalization.* `D5/S0/Certificates/TracePartitionRefutation.Equality` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite congruence derivation uses original trace roots and same-symbol edges.

**Theorem 1.3 (equality sound).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.equality_sound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TracePartitionRefutation.equality_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every derived equality holds in each fitted existing skeleton that respects the branch equalities.

**Definition 1.4 (Refutation).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.Refutation`

*Formalization.* `D5/S0/Certificates/TracePartitionRefutation.Refutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each split keeps every reuse case and a fresh-state case whenever the cardinal budget permits it.

**Theorem 1.5 (refutation sound).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.refutation_sound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TracePartitionRefutation.refutation_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A hypothetical fitted machine follows one retained branch until a proved observation or distinguished-state conflict.

**Theorem 1.6 (refutation excludes fitted skeleton).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.refutation_excludes_fitted_skeleton`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TracePartitionRefutation.refutation_excludes_fitted_skeleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This consumes the original FitsTrace, including partial Option-valued transitions. No new machine semantics is supplied.

**Theorem 1.7 (signature clique card le).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.signature_clique_card_le`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TracePartitionRefutation.signature_clique_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct actual output-return pairs inject into the existing ReturnPairFiber. Merely different variable names do not suffice.

**Theorem 1.8 (simultaneous state signature cost).**

Lean statement: `D5/S0/Certificates/TracePartitionRefutation.simultaneous_state_signature_cost`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TracePartitionRefutation.simultaneous_state_signature_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrent representatives and signature witnesses bound the same canonical state cost. The external checker must establish the pairwise separation premises.

## References

- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.Equality`
- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.Refutation`
- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.Respects`
- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.equality_sound`
- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.refutation_excludes_fitted_skeleton`
- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.refutation_sound`
- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.signature_clique_card_le`
- Truth anchor: `D5/S0/Certificates/TracePartitionRefutation.simultaneous_state_signature_cost`
- Dependency: [D5/S0/Certificates/SkeletonSlotCNF](SkeletonSlotCNF.md)
