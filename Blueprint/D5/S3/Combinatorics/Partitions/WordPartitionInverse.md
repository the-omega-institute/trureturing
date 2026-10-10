# Word reconstruction and the full joint image

## Abstract

Decreasing padded prefix rows, with their endpoint bound, reconstruct one ordered binary word. The full fixed-count, fixed-area joint image is finite and agrees with the image of these actual partitions and of nonempty native trees.

**Theorem 1.1 (The guarded inverse word).**

$$\forall l \in \operatorname{List}\left(Nat\right),\; \operatorname{SortedGE}\left(l\right) \Rightarrow (\forall u \in Nat,\; \left(\forall x \in Nat,\; x \in l \Rightarrow (x \le u)\right) \Rightarrow (\operatorname{count}\left(\operatorname{wordOfRows}\left(u, l\right), true\right) = u \land (\operatorname{count}\left(\operatorname{wordOfRows}\left(u, l\right), false\right) = \operatorname{length}\left(l\right) \land (\operatorname{rows}\left(\operatorname{wordOfRows}\left(u, l\right)\right) = l))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/WordPartitionInverse.wordOfRows_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a decreasing list of natural row lengths bounded by u, build the word by constructing the remaining rows at the first row's endpoint, appending a false letter, then adding the remaining true letters. The resulting word has exactly u true letters and one false letter per row, and its reverse prefix list is exactly the given list. Zero rows and the empty list remain valid.

**Theorem 1.2 (Recovering the same word).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{wordOfRows}\left(\operatorname{count}\left(w, true\right), \operatorname{rows}\left(w\right)\right) = w$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/WordPartitionInverse.wordOfRows_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the construction to the actual reverse prefix rows and true count of any word recovers that very word, including the empty auxiliary word and pure-letter words. This recovers the ordered word; it does not recover forgotten tree brackets.

**Theorem 1.3 (Padding rows by zeros).**

$$\forall u \in Nat,\; \forall l \in \operatorname{List}\left(Nat\right),\; \forall m \in Nat,\; \operatorname{wordOfRows}\left(u, \operatorname{append}\left(l, \operatorname{replicate}\left(m, 0\right)\right)\right) = \operatorname{append}\left(\operatorname{replicate}\left(m, false\right), \operatorname{wordOfRows}\left(u, l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/WordPartitionInverse.wordOfRows_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending zero rows corresponds exactly to prepending that many false letters to the reconstructed word. Zero padding does not replace the core word or normalize its area.

For every natural row list l and natural padding length m, appending m zeros leaves cellsOfRowLens unchanged: upstream YoungDiagram.mem_cellsOfRowLens describes each cell by an entry bound, and List.getElem_append and List.getElem_replicate make every appended row empty. If l is decreasing, List.pairwise_append and List.pairwise_replicate also give decreasing order after padding; YoungDiagram.mem_ofRowLens and YoungDiagram.ext then identify the same diagram and transpose. The padded carrier retains its declared length. These cell and diagram equalities follow directly from the upstream facts.

**Theorem 1.4 (Exact complete-word reversal).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{count}\left(\operatorname{reverse}\left(w\right), true\right) = \operatorname{count}\left(w, true\right) \land (\operatorname{count}\left(\operatorname{reverse}\left(w\right), false\right) = \operatorname{count}\left(w, false\right) \land (\operatorname{scatteredTrueFalseCount}\left(\operatorname{reverse}\left(w\right)\right) = \operatorname{count}\left(w, true\right)\operatorname{count}\left(w, false\right)-\operatorname{scatteredTrueFalseCount}\left(w\right) \land (\operatorname{G}\left(\operatorname{reverse}\left(w\right)\right).e = \operatorname{G}\left(w\right).e \land (\operatorname{G}\left(\operatorname{reverse}\left(w\right)\right).f = \operatorname{G}\left(w\right).f))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/WordPartitionInverse.outer_reverse_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the complete word preserves both counts, complements its scattered pair count within the endpoint rectangle, and preserves both moment coordinates. This is a mathematical comparison of whole words; it grants no reversal operation on an unknown source.

**Definition 1.5 (All guards of the padded partition carrier).**

$$\forall u \in Int,\; \forall v \in Int,\; \forall K \in Int,\; \forall l \in \operatorname{List}\left(Nat\right),\; l \in \operatorname{partitionFiber}\left(u, v, K\right) \Leftrightarrow (0 \le u \land (0 \le v \land (0 < u+v \land (0 \le K \land (K \le uv \land (\operatorname{SortedGE}\left(l\right) \land (\left(\forall x \in Nat,\; x \in l \Rightarrow (x \le \operatorname{toNat}\left(u\right))\right) \land (\operatorname{integer}\left(\operatorname{length}\left(l\right)\right) = v \land (\operatorname{integer}\left(\operatorname{sum}\left(l\right)\right) = K)))))))))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WordPartitionInverse.partitionFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameters are arbitrary integers. Each carrier list has natural entries, is decreasing, is bounded by the natural part of u, has length v and sum K after casting to the integers, and satisfies all endpoint, nonemptiness and area guards. No area complement or deletion of zero rows is part of this carrier.

**Definition 1.6 (Both moments of one list).**

$$\forall u \in Int,\; \forall v \in Int,\; \forall K \in Int,\; \forall l \in \operatorname{List}\left(Nat\right),\; \operatorname{partitionOutput}\left(u, v, K, l\right) = (\operatorname{real}\left(u\right)^{2}\operatorname{real}\left(v\right)-6\operatorname{real}\left(u\right)\operatorname{real}\left(K\right)+6\operatorname{squareRows}\left(l\right),-\operatorname{real}\left(u\right)\operatorname{real}\left(v\right)^{2}+6\operatorname{real}\left(v\right)\operatorname{real}\left(K\right)-6\operatorname{oddRows}\left(l\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/WordPartitionInverse.partitionOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer parameters are cast to the reals. squareRows is the sum of the squared real casts of the entries. oddRows weights the entries, starting at index zero, by one, three, five and so on. Both coordinates use the same l.

**Theorem 1.7 (The full nonempty actual joint image).**

$$\forall u \in Int,\; \forall v \in Int,\; \forall K \in Int,\; \operatorname{Finite}\left(\operatorname{jointImage}\left(u, v, K\right)\right) \land (\operatorname{nativeImage}\left(u, v, K\right) = \operatorname{jointImage}\left(u, v, K\right) \land (\operatorname{jointImage}\left(u, v, K\right) = \operatorname{image}\left(\operatorname{partitionOutput}\left(u, v, K\right), \operatorname{partitionFiber}\left(u, v, K\right)\right) \land (\operatorname{jointImage}\left(u, v, K\right) = \operatorname{jointImage}\left(u, v, uv-K\right) \land (\operatorname{capacity}\left(u, v, K\right) = \operatorname{ncard}\left(\operatorname{nativeImage}\left(u, v, K\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/WordPartitionInverse.finite_joint_partition_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary integer endpoint and pair-count parameters, take every nonempty binary word with those exact counts. Their distinct joint moment outputs form a finite set, since each word has the fixed length u plus v. This set equals the image of decreasing natural row lists with nonnegative integer parameters u, v and K, positive u plus v, K at most u times v, each row at most u, exactly v entries and sum K. A row list l gives the simultaneous pair (u squared times v - 6uK + 6 squareRows(l), minus u times v squared + 6vK - 6 oddRows(l)). The same set also equals the moment image of native nonempty ordered binary trees. Complete-word reversal identifies this same joint image with the complementary pair count, and its capacity equals the native image cardinality. Negative counts, invalid pair counts and the empty endpoint produce no word source. Each nonempty word has the displayed left-comb representative; recovering an actual tree requires an additional left-comb promise. A representative supplies no physical acquisition, source-membership certification, mutation, calibration or other source authority. No sparse capacity bound or thick-frame family inverse is asserted here.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/WordPartitionInverse.finite_joint_partition_image`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WordPartitionInverse.outer_reverse_contract`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WordPartitionInverse.partitionFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WordPartitionInverse.partitionOutput`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WordPartitionInverse.wordOfRows_inverse`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WordPartitionInverse.wordOfRows_padding`
- Truth anchor: `D5/S3/Combinatorics/Partitions/WordPartitionInverse.wordOfRows_spec`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](../../Arith/FibonacciAtomic/GenealogicalFiberTransport.md)
- Dependency: [D5/S3/Combinatorics/Partitions/PaddedWordPartition](PaddedWordPartition.md)
- Dependency: [D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery](../../Observer/GoldenChronology/GoldenMagnusParityRecovery.md)
