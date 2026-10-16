# Native literal cut rows and actual collision sources

## Abstract

Finite Boolean trees retain their complete cut exterior and hole partition.

**Definition 1.1 (Public finite cuts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.CutSet`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.CutSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cuts are finite List Bool address sets. The empty set and the root address are included.

**Definition 1.2 (Native prefix freedom).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.CutPrefixFree`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.CutPrefixFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Prefix freedom uses the existing IsPrefixFree relation without an additional cut theory.

**Definition 1.3 (Literal observable term).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A FreeMagma (Bool ⊕ Nat) term retains every exterior constructor and concrete Boolean leaf. Each hole carries the first lexicographic reached-hole ordinal in its actual subtree-equality class, rather than its value or size.

**Theorem 1.4 (Canonical class equality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.classOrdinal_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.classOrdinal_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On reached cuts, equality of first-occurrence ordinals is exactly equality of native subtree options. List.idxOf_inj supplies the first-occurrence fact.

**Theorem 1.5 (Structural hole support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_hole_support_aux`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_hole_support_aux` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extracting addresses from a local literal expression recovers its structural reached-hole support.

**Theorem 1.6 (Canonical hole support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_hole_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_hole_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hole addresses can be extracted from the observable term itself, including the zero-hole and root-hole cases.

**Definition 1.7 (Finite row navigation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.rowAt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.rowAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Navigation inspects only the retained expression. A concrete or hole leaf prevents any further descent.

**Definition 1.8 (Actual label extraction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.holeLabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.holeLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label extractor returns a natural-number class marker only when the navigated term is a hole leaf.

**Theorem 1.9 (Exterior readout bridge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_at`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If no strict ancestor is a cut, navigating the literal expression agrees with native subtree navigation followed by the local cut expression. Thus exterior constructors and Boolean leaves remain readable.

**Theorem 1.10 (Reached cut readout).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_at_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_at_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a public cut the row contains exactly its class marker when the native subtree exists, and is absent otherwise.

**Theorem 1.11 (Precise reached support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_reached`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_reached` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The holes extracted from canonicalRow are exactly the public cuts intersected with the actual tree positions.

**Theorem 1.12 (Ordered support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.orderedHoles_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.orderedHoles_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sorting the extracted support retains exactly the reached public cuts.

**Theorem 1.13 (Equality and disequality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality and disequality of labels actually extracted from the term agree with equality and disequality of all reached native hole values.

**Theorem 1.14 (Concrete absence guards).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_absent_guard`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_absent_guard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every absent public cut has a strict-prefix Boolean leaf visible in the retained exterior.

**Theorem 1.15 (Common proof evaluation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_evaluate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_evaluate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single valuation of the global old labels reconstructs every reached local source. This valuation is used only in proofs; it is not available to a decoder. No injectivity of arbitrary substitution is asserted.

**Definition 1.16 (Finite public suffix section).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A section filters public cuts with a given prefix and drops that prefix.

**Theorem 1.17 (Exact section membership).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.mem_cutSection_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.mem_cutSection_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Section membership is exactly membership of the concatenated address in the original cut.

**Theorem 1.18 (Section concatenation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection_mem_append`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection_mem_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A suffix in a section reconstructs a member of the original public cut.

**Definition 1.19 (Common-suffix equation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.HasCommonSuffix`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.HasCommonSuffix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite prefix-free S witnesses P = {q ++ s : q ∈ Q, s ∈ S}.

**Theorem 1.20 (Empty product).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.commonSuffix_empty_right`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.commonSuffix_empty_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common-suffix equation with Q empty holds exactly when P is empty.

**Theorem 1.21 (Root product).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.commonSuffix_root_right`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.commonSuffix_root_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prefix-free P is the product of the root cut with P. Recovery follows only after the decoder and kernel classification are supplied.

**Theorem 1.22 (Prefix-free sections).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection_prefixFree`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection_prefixFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each suffix section of a prefix-free public cut remains prefix-free.

**Definition 1.23 (Actual finite prefix trie).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.prefixTrie`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.prefixTrie` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A depth bounded by the maximum public address length reaches every cut. Unused branches are concrete alpha leaves, and each cut is filled by a native finite source.

**Theorem 1.24 (Actual subtree at a trie cut).**

$$\forall n: Nat, (\forall P: CutSet, (\forall a, r: Address, (\forall f: Address \to Source, (((\operatorname{append}\left(a, r\right) \in P) \land (\operatorname{length}\left(r\right) \leq n) \land (\forall s: Address, ((\operatorname{IsPrefix}\left(s, r\right)) \implies ((s \neq r) \implies (\neg \operatorname{append}\left(a, s\right) \in P))))) \implies (\operatorname{subtree}\left(r, \operatorname{prefixTrie}\left(n, P, a, f\right)\right) = \operatorname{some}\left(\operatorname{f}\left(\operatorname{append}\left(a, r\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.prefixTrie_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original trie lemma reaches a ++ r within the supplied depth, provided no strict prefix of r enters the cut. Its unchanged proof is directly consumed by OriginalVector.InterleavedWordRecovery.original_at. Choosing the entire level retains the complete source skeleton, including all unselected leaves.

**Theorem 1.25 (Uniform old-row collision).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.uniform_trie_row`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.uniform_trie_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniformly filling the same trie with any two sources gives the same complete old row: its exterior and its single equality class agree.

**Theorem 1.26 (Uncovered-hole source pair).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.coverage_failure_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.coverage_failure_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fill every P hole with alpha or every P hole with beta. If one old cut has no Q prefix, its leaf remains visible in the Q exterior, so these actual sources have equal old rows and different new rows.

**Theorem 1.27 (First matching position under a relation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.idxOf_map_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.idxOf_map_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two finite mapped value lists have the same first matching position when equality to the target agrees at every list entry. The fact is consumed by class preservation and decoder renaming.

**Definition 1.28 (One-class path marker).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.markerContext`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.markerContext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H_nil a = a; at a false step form mul (H_r a) beta, and at a true step form mul beta (H_r a). Alpha occurs as a complete subtree only at the selected suffix.

**Definition 1.29 (Native row kernel inclusion).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.Recovers`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.Recovers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recovery means that equal old canonical rows imply equal new canonical rows for every pair of finite nonempty Boolean sources.

**Theorem 1.30 (Necessary prefix coverage).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.recovery_covers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.recovery_covers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual uncovered-hole collision excludes recovery whenever an old hole lacks a new-cut prefix.

**Theorem 1.31 (Simultaneous whole-class preservation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.nonuniform_old_row`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.nonuniform_old_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t = H_s alpha and z = mul t beta. Fill one Q-prefix trie with t; in the other, fill q with H_s z exactly when q ++ s belongs to P. All alpha-valued old holes change together to the fresh z. All other actual values, absent cuts, exterior syntax, and class disequalities remain.

**Theorem 1.32 (Nonuniform source separation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.nonuniform_failure_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.nonuniform_failure_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x ++ s belongs to P and y ++ s does not, the two actual sources have equal complete P rows. Their Q subtrees at x and y were equal and become different. Native subtree leaf-count bounds prove z is fresh, without requiring all P addresses to be reached.

**Theorem 1.33 (Actual present class value).**

$$\forall P: CutSet, (\forall u: Source, (\forall p: Address, (\forall t: Source, (((\operatorname{CutPrefixFree}\left(P\right)) \land (p \in P) \land (\operatorname{subtree}\left(p, u\right) = \operatorname{some}\left(t\right))) \implies (\operatorname{classValue}\left(P, u, \operatorname{classOrdinal}\left(P, u, p\right)\right) = t)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.classValue_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an originally reached cut, the canonical class valuation equals its actual native subtree. The prefix-free and original-presence premises are retained. The same supplier supports reconstruction and all-class injectivity.

The source domain is every finite nonempty ordered Boolean-leaf tree, and the cuts have no depth or common-shape restriction. The later decoder and classification consume these actual source pairs. This mathematical record makes no physical acquisition or resource-cost assertion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.CutPrefixFree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.CutSet`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.HasCommonSuffix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.Recovers`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_absent_guard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_at_cut`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_partition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.canonicalRow_reached`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.classOrdinal_eq_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.classValue_at`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.commonSuffix_empty_right`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.commonSuffix_root_right`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.coverage_failure_pair`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection_mem_append`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.cutSection_prefixFree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.holeLabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.idxOf_map_relation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_at`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_evaluate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_hole_support`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.literalRow_hole_support_aux`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.markerContext`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.mem_cutSection_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.nonuniform_failure_pair`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.nonuniform_old_row`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.orderedHoles_mem`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.prefixTrie`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.prefixTrie_at`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.recovery_covers`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.rowAt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.uniform_trie_row`
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](../../../../S0/Computability/Coding/PrefixFreeCode.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination](../ActualFiniteObserverAbsentElimination.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](../ActualImageAlphaSeparation.md)
