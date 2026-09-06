# General-Carrier Clerk Inequalities

## Abstract

Fresh permanent records bound arbitrary semantic snapshots in ENat.

**Theorem 1.1 (The two inequalities on arbitrary sets).**

$$\begin{aligned}\forall u, v: \operatorname{Level}, \forall S: \operatorname{Type}(u), G: \operatorname{Type}(v),\\\forall r, t\in \mathbb{N}, \forall H: \operatorname{SetClerkHistory}(S, G, r),\\r \geq 1 \Rightarrow ((r: \operatorname{ENat}) \cdot \operatorname{cumulativeMigrations}(H, t) \leq \operatorname{encard}(\operatorname{semanticAt}(H, t))\\\land \operatorname{encard}(\operatorname{semanticAt}(H, 0)) + ((r - 1: \mathbb{N}): \operatorname{ENat}) \cdot \operatorname{cumulativeMigrations}(H, t) \leq \operatorname{encard}(\operatorname{semanticAt}(H, t)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Accounting/GeneralCarrierClerkInequality.clerk_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SetClerkHistory extends the existing LedgerHistory enrollment and grading carrier. A statement is semantic at t exactly when it is enrolled by t and its grade is outside theoremGrade. It migrates at t exactly when it is semantic at t and has a theorem grade at t + 1. Semantic, migration, and record snapshots are arbitrary sets.

The history certificate requires every record at t to be newly enrolled after t and semantic at every u at least t + 1. It also requires encard(recordsAt(t)) to be at least r times encard(migrationsAt(t)). The coefficient r is a natural number; r minus one is computed in Nat before coercion to ENat.

Here cumulativeMigrations(H,t) is the ENat sum of encard(migrationsAt(H,i)) over i in Finset.range(t). ENat is the extended natural numbers and encard is Set.encard. No countability of statements, finiteness or order on grades, or upper closure of theoremGrade is required.

Freshness and permanence prove that record batches at distinct ticks are disjoint. The cumulative_record_bound lemma places the sum of all earlier record encards below the current semantic encard. Combining it with the quotas proves the first clause. For the second clause, semantic_step_bound partitions the previous snapshot into migrants and survivors, adds disjoint fresh records, and cumulative_step_bound iterates the estimate.

Repository and pinned Mathlib searches found the finite ClerkHistory owner and the general set-cardinality primitives, but no complete general-carrier clerk theorem. The derivation uses Set.encard_sdiff_add_encard_of_subset, Set.encard_union_eq, Set.encard_iUnion_of_finite, Finset.sum_le_sum, and Finset.sum_range_succ. The accounting statement is repo-derived.

**Theorem 1.2 (Specialization to the finite owner).**

$$\begin{aligned}\forall u, v: \operatorname{Level}, \forall S: \operatorname{Type}(u), G: \operatorname{Type}(v),\\\forall r, t\in \mathbb{N}, \forall H: \operatorname{ClerkHistory}(S, G, r),\\r \geq 1 \Rightarrow (r \cdot \operatorname{cumulativeMigrations}(H, t) \leq \operatorname{card}(\operatorname{semanticAt}(H, t))\\\land \operatorname{card}(\operatorname{semanticAt}(H, 0)) + (r - 1: \mathbb{N}) \cdot \operatorname{cumulativeMigrations}(H, t) \leq \operatorname{card}(\operatorname{semanticAt}(H, t)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Accounting/GeneralCarrierClerkInequality.finite_clerk_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here ClerkHistory and cumulativeMigrations are the frozen finite definitions in ClerkInequality, and card is Finset.card. The map ofFinite coerces all three snapshots to sets and preserves the same enrollment, grading, and accounting certificate. Applying the general theorem and reflecting ENat inequalities between natural casts yields exactly the two conclusions of the finite clerk_inequality owner. The proof consumes the general theorem.

## References

- Truth anchor: `D5/S0/History/Accounting/GeneralCarrierClerkInequality.clerk_inequality`
- Truth anchor: `D5/S0/History/Accounting/GeneralCarrierClerkInequality.finite_clerk_inequality`
- Dependency: [D5/S0/History/Accounting/ClerkInequality](ClerkInequality.md)
- Dependency: [D5/S0/History/LedgerLimit](../LedgerLimit.md)
