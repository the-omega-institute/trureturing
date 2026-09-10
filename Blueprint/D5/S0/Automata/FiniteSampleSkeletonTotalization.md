# Finite Sample Skeleton Totalization and Capacity Padding

## Abstract

First-return skeletons admit successful-run-preserving totalization and exact-behavior recurrent capacity padding, with explicit used-signature costs.

**Theorem 1.1 (Total extension with no greater canonical state cost).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.totalization_preserves_success_and_cost`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.totalization_preserves_success_and_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The construction reuses the M17 Skeleton carrier. Missing zero transitions return to the original start state. Each old signature receives one uniform completed return target, and missing one channels reuse a supplied old signature.

The start state and recurrent outputs are retained. Every successful original code evaluation is retained. Undefined runs may become defined, so equality of partial behaviors is not asserted.

**Theorem 1.2 (Completed signatures are images of old used signatures).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.completionMap_surjective`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.completionMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit surjection proves that completion can merge signature classes but cannot create a new class. The old-signature seed supplies the preimage for a previously absent one channel.

**Theorem 1.3 (The start-zero-loop anchor is preserved).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.totalize_preserves_zero_loop`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.totalize_preserves_zero_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An already defined start-state zero self-loop survives the completion. The separate recurrent-output equality preserves the published zero-output anchor.

**Theorem 1.4 (A successful terminal-one observation supplies a seed).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.signature_nonempty_of_transient_success`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.signature_nonempty_of_transient_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonempty-signature premise can be derived from sample data containing a successful transient-channel observation. It is not assumed for an arbitrary empty-observation problem.

**Theorem 1.5 (An empty signature set prevents zero-cost totalization).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.empty_signature_cost_obstruction`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.empty_signature_cost_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A total skeleton has a defined one channel at its start state and therefore has at least one used transient signature. An original signature count of zero cannot be preserved.

**Theorem 1.6 (Transport a fitted sample family to a total realization).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.exists_total_sample_realization`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.exists_total_sample_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One successful transient observation suffices for the construction. All labels in the supplied family remain correct, on the same recurrent carrier and at no greater canonical state cost. No CNF, SAT refutation, or numerical DFAO lower bound is claimed here.

**Theorem 1.7 (Total signature cost is ordinary output-return pair cost).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.total_canonical_cost_eq_pair_cost`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.total_canonical_cost_eq_pair_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Totality makes every used optional return target present. Removing this wrapper gives an equivalence with used ordinary output-return pairs and preserves cardinality.

**Theorem 1.8 (At most one used signature per recurrent source).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.signature_card_le_recurrent_card`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.signature_card_le_recurrent_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Determinism makes the choice of one recurrent source per used signature injective. This gives the source-count constraint used by the capacity search.

**Theorem 1.9 (Capacity padding preserves defined and undefined evaluations).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.eval_padSkeleton`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.eval_padSkeleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is the sum of the original carrier and extra capacity. Each extra state emulates the original start, while all transition targets remain in the original summand. Evaluation from any padded state agrees with evaluation from its collapsed original state, including none results.

**Theorem 1.10 (Extra recurrent states request no new signature).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.paddingSignatureMap_surjective`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.paddingSignatureMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A padded state's signature request is the embedded request of its collapsed original source. Thus every used padded signature has an original preimage. Together with injectivity of embedded return targets, this yields an exact bijection of used signatures.

**Theorem 1.11 (Used signature cardinality is exactly unchanged).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_signature_card_eq`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_signature_card_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Capacity padding neither merges nor adds used signatures. This theorem permits an empty original signature set because padding does not fill undefined transitions.

**Theorem 1.12 (Padding preserves totality).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_isTotal`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_isTotal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every original transition and return is defined, each added start-state copy is total as well. A separate companion preserves the start-zero-loop, and the start output is unchanged.

**Theorem 1.13 (Canonical state cost increases only by allocated recurrent capacity).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_canonical_state_card`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_canonical_state_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signature cost is identical, while the recurrent carrier gains exactly the chosen number of extra states. Padding does not claim that total state cost itself remains unchanged.

**Theorem 1.14 (Represent the same behavior at any larger recurrent capacity).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.exists_fixed_capacity_padding`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.exists_fixed_capacity_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The construction allocates the finite capacity difference, preserves all block-code evaluations and exact used-signature cost, and transports totality when supplied. This is intended for the M19.3 weighted fixed-capacity consumer. It permits unused states; it does not justify an encoding requiring every allocated state to be reachable.

**Theorem 1.15 (Conditional arithmetic coverage of the fourteen-state budget).**

Lean statement: `D5/S0/Automata/FiniteSampleSkeletonTotalization.budget_fourteen_capacity_cover`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleSkeletonTotalization.budget_fourteen_capacity_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a total budget of fourteen, the source-count bound, and a separately proved signature lower bound of three, five capacity rectangles suffice. This companion proves only arithmetic coverage. It supplies neither the sample-specific lower bound of three nor any UNSAT certificate.

## References

- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.budget_fourteen_capacity_cover`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.completionMap_surjective`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.empty_signature_cost_obstruction`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.eval_padSkeleton`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.exists_fixed_capacity_padding`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.exists_total_sample_realization`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_canonical_state_card`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_isTotal`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.pad_signature_card_eq`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.paddingSignatureMap_surjective`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.signature_card_le_recurrent_card`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.signature_nonempty_of_transient_success`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.total_canonical_cost_eq_pair_cost`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.totalization_preserves_success_and_cost`
- Truth anchor: `D5/S0/Automata/FiniteSampleSkeletonTotalization.totalize_preserves_zero_loop`
- Dependency: [D5/S0/Automata/BinaryZeckendorfBlockSkeleton](BinaryZeckendorfBlockSkeleton.md)
