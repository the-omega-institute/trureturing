# Recurrent-State Conjugacy of First-Return Skeletons

## Abstract

Explicit recurrent-state equivalences preserve partial evaluation and canonical cost, allowing verified zero-map witnesses to cover the finite search.

**Definition 1.1 (Reindex the recurrent carrier).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.reindex`

*Formalization.* `D5/S0/Automata/SkeletonStateConjugacy.reindex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The start, zero target and optional signature return are transported by one equivalence. Original output and partial-run semantics remain the owners.

**Theorem 1.2 (Transport every continuation).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.evalFrom_reindex`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.evalFrom_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the original return blocks proves equality for arbitrary continuations, including unsuccessful partial runs.

**Theorem 1.3 (Preserve start-state evaluation).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.eval_reindex`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.eval_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same original block code has exactly the same output after carrier renaming.

**Definition 1.4 (Transport used signatures).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.signatureMap`

*Formalization.* `D5/S0/Automata/SkeletonStateConjugacy.signatureMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An old output-return signature maps to a used signature of the reindexed skeleton. Its return uses the same carrier equivalence.

**Theorem 1.5 (No signature is identified).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.signatureMap_injective`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.signatureMap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the inverse equivalence to the return coordinate recovers the old signature.

**Theorem 1.6 (No new signature is introduced).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.signatureMap_surjective`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.signatureMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every new signature is witnessed by an original one transition at the inverse image of its source.

**Theorem 1.7 (Preserve exact state cost).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.canonical_cost_reindex`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.canonical_cost_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrent carriers and the actual used-signature carriers are bijective. Their sum, the existing canonical cost, is unchanged even with unused states.

**Theorem 1.8 (Use the explicit zero-map witness).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.zero_row_conjugacy`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.zero_row_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An entry-by-entry conjugacy identity yields exactly the representative zero row on the reindexed candidate.

**Theorem 1.9 (Preserve the initial loop).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.initial_zero_loop_reindex`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.initial_zero_loop_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The designated initial zero self-loop survives the same transport. No ordinary self-loop is excluded.

**Theorem 1.10 (Lift representative exclusions to all covered zero maps).**

Lean statement: `D5/S0/Automata/SkeletonStateConjugacy.covered_zero_maps_refute_samples`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SkeletonStateConjugacy.covered_zero_maps_refute_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every cover entry is supported by a real state equivalence fixing the root. Evaluation and exact-cost transport construct the contradiction to its representative exclusion. Concrete cover validation and numerical representative refutations remain separate proof inputs.

## References

- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.canonical_cost_reindex`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.covered_zero_maps_refute_samples`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.evalFrom_reindex`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.eval_reindex`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.initial_zero_loop_reindex`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.reindex`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.signatureMap`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.signatureMap_injective`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.signatureMap_surjective`
- Truth anchor: `D5/S0/Automata/SkeletonStateConjugacy.zero_row_conjugacy`
- Dependency: [D5/S0/Automata/BinaryZeckendorfBlockSkeleton](BinaryZeckendorfBlockSkeleton.md)
