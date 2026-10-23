# Finite source-free recutting

## Abstract

Finite retained expressions determine common-suffix recuts.

**Definition 1.1 (Reached new addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.decoderHoles`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.decoderHoles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite navigation of the retained old expression identifies the reached Q addresses and orders them lexicographically.

**Definition 1.2 (Global-label comparison).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.decoderClass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.decoderClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each extracted local expression retains the same global old class names. Syntactic equality of these finite expressions determines the first new class ordinal.

**Definition 1.3 (Literal exterior recutting).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.recutRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.recutRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Traverse the old term and replace each reached new cut by its new canonical hole label, copying all remaining constructors and concrete leaves.

**Definition 1.4 (Total finite decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.rowDecoder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.rowDecoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoder takes Q and the retained old term only. It neither selects a realizing source nor receives hidden hole values. It is total on raw terms and correct on all realized common-suffix rows.

**Theorem 1.5 (Exact local-expression kernel).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.common_local_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.common_local_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under P = Q S, two extracted local terms are equal exactly when their actual Q subtrees are equal, including absent addresses. Forward evaluation uses the same proof valuation. Reverse equality cuts the same actual subtree synchronously by the same suffix S.

**Theorem 1.6 (Exact row computation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_decoder_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_decoder_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual source, common-suffix cuts make rowDecoder return its precise canonical Q row, preserving the exterior, reached set, absence guards, and complete partition.

**Theorem 1.7 (Sufficient recovery).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_recovers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_recovers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal old rows give equal decoder outputs, hence equal new rows. The decoder supplies the native kernel inclusion.

**Theorem 1.8 (Unique nonempty suffix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty prefix-free Q, each q section computes the same S. Prefix ownership and cancellation prove uniqueness.

**Definition 1.9 (Finite cut concatenation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.cutProduct`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.cutProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite union and image compute all q ++ s for q in Q and s in S.

**Definition 1.10 (Executable finite comparison).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffixTest`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffixTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sort Q. If empty, compare P with the empty set. Otherwise take its first q, compute cutSection P q, and compare P with the finite cut product. Every operation has finite decidable equality.

**Theorem 1.11 (Exact decision criterion).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffixTest_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffixTest_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite prefix-free P and Q, the Boolean comparison returns true exactly when a finite prefix-free common suffix exists.

**Definition 1.12 (Independently addressed exterior).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.HoleExterior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.HoleExterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each hole is named by its native address. Sorting these unique addresses gives the lexicographic hole numbering, while every exterior constructor and concrete Boolean leaf remains literal.

**Definition 1.13 (Literal exterior computation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.cutExterior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.cutExterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Stop at public cuts, mark the reached hole by its address, and copy every constructor and concrete leaf outside the cuts. The result contains no hole value.

**Definition 1.14 (Complete finite partition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.actualPartition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.actualPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set contains exactly the pairs of reached holes with equal actual subtrees. Every other reached pair records a genuine disequality.

**Definition 1.15 (Exterior and partition record).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.literalRecord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.literalRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This pair computes the addressed exterior and the complete finite partition independently of the class-labelled row representation.

**Definition 1.16 (Address-to-role naming).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.nameExterior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.nameExterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any total function names from original addresses to natural numbers, nameExterior is the free-magma lift sending a concrete Boolean leaf to that same literal leaf and an addressed hole p to the role leaf names(p). It preserves every ordered binary pair and every occurrence, including repeated role names. It neither reads a source nor requires names to be injective, and it applies to ground exteriors and a single root hole.

**Theorem 1.17 (Exact structural naming).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.nameExterior_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.nameExterior_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary prefix-free P, root, names, address a and finite subtree t, if names agrees with classOrdinal at every reached ordered P hole and subtree a root is some t, then nameExterior names (cutExterior P a t) equals literalRow P root a t. Both concrete leaves and all reached cut holes are preserved. The statement includes empty and root cuts and arbitrary subtrees of the same root. Together with exteriorHoles_cut and findIdx/idxOf normalization, this structural naming result identifies recordRow of an actual literalRecord with canonicalRow without another structural decoder.

**Theorem 1.18 (Faithful representation bridge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.canonicalRow_record_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.canonicalRow_record_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two sources have the same canonicalRow exactly when their independent exterior and complete partition records agree. The forward direction extracts the exterior and partition. The reverse direction fixes the same reached-hole ordering and first matching indices, then renames the same exterior. Consequently the canonical representation carries exactly the record information, including empty and root holes, without disclosing hidden values, sizes or acquisition traces.

**Theorem 1.19 (Independent exterior hole support).**

$$\forall P: CutSet, (\forall a: Address, (\forall t: Source, (\operatorname{exteriorHoles}\left(a, \operatorname{cutExterior}\left(P, a, t\right)\right) = \operatorname{reachedHoles}\left(P, a, t\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.exteriorHoles_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading address-marked holes from the actual exterior recovers exactly the reached cuts. This independent support bridge retains original absent cuts and the empty/root cases.

The decoder compares actual retained syntax, not independently renumbered local partitions. Arbitrary substitution injectivity is not used. Absence is determined by visible strict-prefix leaves. The finite decision procedure examines public words only; it does not inspect a source.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.HoleExterior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.actualPartition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.canonicalRow_record_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffixTest`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffixTest_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_decoder_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_recovers`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.commonSuffix_unique`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.common_local_kernel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.cutExterior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.cutProduct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.decoderClass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.decoderHoles`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.exteriorHoles_cut`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.literalRecord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.nameExterior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.nameExterior_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.recutRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.rowDecoder`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery](ActualCutPartitionRecovery.md)
