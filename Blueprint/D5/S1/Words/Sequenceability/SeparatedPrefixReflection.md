# Affine prefix geometry on actual words

## Abstract

Separated reflection and repair in the SAME legal compression space.

All objects live in the original arbitrary additive commutative group. The operation reverses actual letters in [h,k), with coefficient one. The affine involution x -> lo+hi-x describes prefix values. Separation is required; this is not an unconditional group action on all Good orders.

**Definition 1.1 (All bounded prefix sums).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; \forall i \in Nat,\; pref\left(w, i\right) = sum\left(take\left(i, w\right)\right)$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.pref` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Empty and full cuts are included. take and drop take the count first.

**Definition 1.2 (Proper zero-sum intervals).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; (Good\left(w\right)) \Leftrightarrow (\forall i \in Nat,\; \forall j \in Nat,\; ((i < j) \land ((j \le length\left(w\right)) \land ((i \ne 0) \lor (j \ne length\left(w\right))))) \Rightarrow (sum\left(take\left(j - i, drop\left(i, w\right)\right)\right) \ne 0))$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.Good` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full interval alone is exempt, preserving the zero-total convention.

**Definition 1.3 (Strict additive cone).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall C \in Set\left(G\right),\; (StrictCone\left(C\right)) \Leftrightarrow ((\neg mem\left(0, C\right)) \land (\forall x \in G,\; \forall y \in G,\; ((mem\left(x, C\right)) \land (mem\left(y, C\right))) \Rightarrow (mem\left(x + y, C\right))))$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.StrictCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only addition closure and exclusion of zero are assumed.

**Definition 1.4 (Reflexive cone comparison).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall C \in Set\left(G\right),\; \forall x \in G,\; \forall y \in G,\; (ConeLE\left(C, x, y\right)) \Leftrightarrow ((x = y) \lor (mem\left(y - x, C\right)))$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.ConeLE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Comparison need not be total.

**Definition 1.5 (Actual block reversal).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; \forall h \in Nat,\; \forall k \in Nat,\; reverseBlock\left(w, h, k\right) = append\left(append\left(take\left(h, w\right), reverse\left(take\left(k - h, drop\left(h, w\right)\right)\right)\right), drop\left(k, w\right)\right)$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.reverseBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual occurrence letters are reversed, including endpoint-touching blocks.

**Definition 1.6 (All prefix values).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; inventory\left(w\right) = image\left(pref\left(w\right), range\left(length\left(w\right) + 1\right)\right)$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.inventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finset records values of every cut, including both endpoint cuts.

**Definition 1.7 (Removed prefix values).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; \forall h \in Nat,\; \forall k \in Nat,\; interior\left(w, h, k\right) = image\left(pref\left(w\right), Ioo\left(h, k\right)\right)$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.interior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Interior cuts of a Good word have distinct values.

**Definition 1.8 (Added prefix values).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; \forall h \in Nat,\; \forall k \in Nat,\; \forall lo \in G,\; \forall hi \in G,\; reflected\left(w, h, k, lo, hi\right) = image\left(\operatorname{fun} (x: G) \mapsto lo + hi - x, interior\left(w, h, k\right)\right)$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.reflected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine involution is injective by cancellation.

**Definition 1.9 (Input excursion separation).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; \forall h \in Nat,\; \forall k \in Nat,\; \forall lo \in G,\; \forall hi \in G,\; \forall C \in Set\left(G\right),\; (Separated\left(C, w, h, k, lo, hi\right)) \Leftrightarrow ((((pref\left(w, h\right) = lo) \land (pref\left(w, k\right) = hi)) \lor ((pref\left(w, h\right) = hi) \land (pref\left(w, k\right) = lo))) \land ((ConeLE\left(C, lo, hi\right)) \land ((\forall i \in Nat,\; ((h < i) \land (i < k)) \Rightarrow (mem\left(pref\left(w, i\right) - hi, C\right))) \land (\forall j \in Nat,\; ((j \le length\left(w\right)) \land ((j \le h) \lor (k \le j))) \Rightarrow (ConeLE\left(C, lo, pref\left(w, j\right)\right))))))$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.Separated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both endpoint orientations are admitted. Coincident endpoints include the full zero-total case.

**Theorem 1.10 (Exact reflection and inventory replacement).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall C \in Set\left(G\right),\; \forall w \in List\left(G\right),\; \forall h \in Nat,\; \forall k \in Nat,\; \forall lo \in G,\; \forall hi \in G,\; ((StrictCone\left(C\right)) \land ((Good\left(w\right)) \land ((2 \le k - h) \land ((k \le length\left(w\right)) \land (Separated\left(C, w, h, k, lo, hi\right)))))) \Rightarrow ((Perm\left(reverseBlock\left(w, h, k\right), w\right)) \land ((length\left(reverseBlock\left(w, h, k\right)\right) = length\left(w\right)) \land ((sum\left(reverseBlock\left(w, h, k\right)\right) = sum\left(w\right)) \land ((\forall j \in Nat,\; ((j \le length\left(w\right)) \land ((j \le h) \lor (k \le j))) \Rightarrow (pref\left(reverseBlock\left(w, h, k\right), j\right) = pref\left(w, j\right))) \land ((\forall j \in Nat,\; ((h \le j) \land (j \le k)) \Rightarrow (pref\left(reverseBlock\left(w, h, k\right), j\right) = pref\left(w, h\right) + pref\left(w, k\right) - pref\left(w, h + k - j\right))) \land ((Good\left(reverseBlock\left(w, h, k\right)\right)) \land ((Disjoint\left(reflected\left(w, h, k, lo, hi\right), inventory\left(w\right)\right)) \land ((inventory\left(reverseBlock\left(w, h, k\right)\right) = union\left(sdiff\left(inventory\left(w\right), interior\left(w, h, k\right)\right), reflected\left(w, h, k, lo, hi\right)\right)) \land ((sdiff\left(inventory\left(w\right), inventory\left(reverseBlock\left(w, h, k\right)\right)\right) = interior\left(w, h, k\right)) \land ((sdiff\left(inventory\left(reverseBlock\left(w, h, k\right)\right), inventory\left(w\right)\right) = reflected\left(w, h, k, lo, hi\right)) \land ((card\left(interior\left(w, h, k\right)\right) = k - h - 1) \land ((card\left(reflected\left(w, h, k, lo, hi\right)\right) = k - h - 1) \land (0 < k - h - 1)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.separated_prefix_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the actual list into L,M,R and reverse M. Summing a prefix of reverse(M) gives the suffix sum of M and hence the exact reflection formula. Every old interior value is above lo, while every reflected value is below lo. Exterior old values are at least lo. Cone closure would put zero in C if a reflected value equaled any old value, proving disjointness from the entire old inventory. Old Good gives interior injectivity and excludes exterior/interior aliases. Thus the retained exterior set is exactly S minus I, and no new cut equality appears. The only surviving possible equality is the original empty/full one. This proof covers either endpoint orientation, zero total, and endpoint-touching blocks. Reflection and cut reflection are injective, so exactly k-h-1 values are removed and added. This is the substantive construction consumed immediately by same_pair_repair.

**Definition 1.11 (Prescribed adjacent expansion).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; \forall t \in Nat,\; \forall a \in G,\; \forall b \in G,\; expandAt\left(w, t, a, b\right) = append\left(take\left(t, w\right), cons\left(a, cons\left(b, drop\left(t + 1, w\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.expandAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At the supplied occurrence of a+b, replace only that occurrence with adjacent a,b.

**Definition 1.12 (Same legal-pair alphabet).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall A \in Finset\left(G\right),\; \forall a \in G,\; \forall b \in G,\; compressed\left(A, a, b\right) = insert\left(a + b, erase\left(erase\left(A, a\right), b\right)\right)$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.compressed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Legality makes the merged label new and restores exactly A after expansion.

**Definition 1.13 (Actual Good compression space).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall A \in Finset\left(G\right),\; \forall a \in G,\; \forall b \in G,\; \forall w \in List\left(G\right),\; (Omega\left(A, a, b, w\right)) \Leftrightarrow ((Perm\left(w, toList\left(compressed\left(A, a, b\right)\right)\right)) \land (Good\left(w\right)))$$

*Formalization.* `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.Omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Omega consists of actual permutations, with no successful-expansion premise.

**Theorem 1.14 (Prescribed SAME-pair collision repair).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall C \in Set\left(G\right),\; \forall A \in Finset\left(G\right),\; \forall a \in G,\; \forall b \in G,\; \forall w \in List\left(G\right),\; \forall t \in Nat,\; \forall h \in Nat,\; \forall k \in Nat,\; \forall lo \in G,\; \forall hi \in G,\; ((StrictCone\left(C\right)) \land ((\neg mem\left(0, A\right)) \land ((mem\left(a, A\right)) \land ((mem\left(b, A\right)) \land ((a \ne b) \land ((\neg mem\left(a + b, insert\left(0, A\right)\right)) \land ((Omega\left(A, a, b, w\right)) \land ((t < length\left(w\right)) \land ((getElem\left(w, t\right) = a + b) \land ((2 \le k - h) \land ((k \le length\left(w\right)) \land ((Separated\left(C, w, h, k, lo, hi\right)) \land (((t < h) \lor (k \le t)) \land (\exists i \in Nat,\; (h < i) \land ((i < k) \land (pref\left(w, t\right) + a = pref\left(w, i\right))))))))))))))))) \Rightarrow ((Omega\left(A, a, b, reverseBlock\left(w, h, k\right)\right)) \land ((reverseBlock\left(w, h, k\right) \ne w) \land ((pref\left(reverseBlock\left(w, h, k\right), t\right) = pref\left(w, t\right)) \land ((\exists q \in t < length\left(reverseBlock\left(w, h, k\right)\right),\; getElem\left(reverseBlock\left(w, h, k\right), t, q\right) = a + b) \land ((\neg mem\left(pref\left(reverseBlock\left(w, h, k\right), t\right) + a, inventory\left(reverseBlock\left(w, h, k\right)\right)\right)) \land ((Good\left(expandAt\left(reverseBlock\left(w, h, k\right), t, a, b\right)\right)) \land ((Perm\left(expandAt\left(reverseBlock\left(w, h, k\right), t, a, b\right), toList\left(A\right)\right)) \land ((sum\left(expandAt\left(reverseBlock\left(w, h, k\right), t, a, b\right)\right) = sum\left(w\right)) \land (\forall x \in G,\; (mem\left(x, expandAt\left(reverseBlock\left(w, h, k\right), t, a, b\right)\right)) \Rightarrow (x \ne 0))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.same_pair_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r=a+b occur at t outside [h,k). Both cuts t and t+1 are exterior, so their prefixes are fixed; their difference proves the actual letter at t is still r. The prescribed inserted value q=P(t)+a is unchanged and belongs to removed I. Exact inventory replacement proves q is absent from the new inventory, rather than assuming a successful expansion. Expansion inserts only q into the prefix path. All old cut equalities retain the endpoint exception and q collides with none, so the expanded word is Good. Permutation cancellation removes the unique new r and inserts the original adjacent a,b, proving the exact A inventory, nonzero labels and unchanged total. The same compression space and legal pair are retained. The collision value witnesses that the new compression differs from the input. No Good A-order, desired cycle/inventory, or extra subset induction is supplied.

**Theorem 1.15 (Original proper-interval and prefix equivalence).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; (Good\left(w\right)) \Leftrightarrow (\forall i \in Nat,\; \forall j \in Nat,\; ((i < j) \land ((j \le length\left(w\right)) \land (pref\left(w, i\right) = pref\left(w, j\right)))) \Rightarrow ((i = 0) \land (j = length\left(w\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.good_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AdaptiveMergePrefix.good_iff_proper_intervals consumes this original equivalence in reverse. Only empty/full equality is exempt, including at zero total.

**Theorem 1.16 (Prefix before an append cut).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall L \in List\left(G\right),\; \forall R \in List\left(G\right),\; \forall j \in Nat,\; (j \le length\left(L\right)) \Rightarrow (pref\left(append\left(L, R\right), j\right) = pref\left(L, j\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.pref_append_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed by AdaptiveMergePrefix.bad_expand_implies_collision to identify a left suffix collision. This is the original normalization helper.

**Theorem 1.17 (Prefix after an append cut).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall L \in List\left(G\right),\; \forall R \in List\left(G\right),\; \forall j \in Nat,\; (length\left(L\right) \le j) \Rightarrow (pref\left(append\left(L, R\right), j\right) = sum\left(L\right) + pref\left(R, j - length\left(L\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.pref_append_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed by AdaptiveMergePrefix.bad_expand_implies_collision to identify a right prefix collision. Both the append cut and the full cut are included.

**Theorem 1.18 (An inventory value has an actual bounded cut).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall w \in List\left(G\right),\; \forall x \in G,\; (mem\left(x, inventory\left(w\right)\right)) \Leftrightarrow (\exists j \in Nat,\; (j \le length\left(w\right)) \land (pref\left(w, j\right) = x))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.mem_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AdaptiveMergePrefix.bad_expand_implies_collision consumes the original finite-image equivalence. All cuts, including empty and full, are represented.

**Theorem 1.19 (A fresh inserted value preserves proper intervals).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall L \in List\left(G\right),\; \forall R \in List\left(G\right),\; \forall a \in G,\; \forall b \in G,\; ((Good\left(append\left(L, cons\left(a + b, R\right)\right)\right)) \land (\neg mem\left(sum\left(L\right) + a, inventory\left(append\left(L, cons\left(a + b, R\right)\right)\right)\right))) \Rightarrow (Good\left(append\left(L, cons\left(a, cons\left(b, R\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.expansion_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original theorem is used contrapositively by AdaptiveMergePrefix.bad_expand_implies_collision. It has no separation or strict-cone hypothesis and includes empty sides and zero-total words.

**Theorem 1.20 (The prescribed expansion restores the original alphabet).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall A \in Finset\left(G\right),\; \forall a \in G,\; \forall b \in G,\; \forall w \in List\left(G\right),\; \forall t \in Nat,\; ((mem\left(a, A\right)) \land ((mem\left(b, A\right)) \land ((a \ne b) \land ((\neg mem\left(a + b, A\right)) \land ((Perm\left(w, toList\left(compressed\left(A, a, b\right)\right)\right)) \land ((t < length\left(w\right)) \land (getElem\left(w, t\right) = a + b))))))) \Rightarrow (Perm\left(expandAt\left(w, t, a, b\right), toList\left(A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.expansion_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AdaptiveMergeRepair.expanded_permutation consumes the original theorem at t = length(L), with w = L ++ [a+b] ++ R and the actual LegalPair membership, distinctness and sum-exclusion facts. This normalization helper is also used by same_pair_repair.

The strict cone is extra structure. A nonempty strict cone cannot exist in a finite group, and the nonempty block interior supplies a cone element. This result does not settle finite torsion, unrestricted adaptive AM, or the original arbitrary-subset, same-M, original-coordinate, coefficient-one parent. The missing global inference is that nonempty Omega for every legal pair forces a usable escape for some actual order. No universal escape, termination, or H-to-cap implication is proved.

Provenance: the supplied standalone native separated-block construction and independent reconstruction supply the argument. The implementation is repo-prior-exposed Codex of the same model family. ChosenMergeExpansionRefutation.Good and expand are specialized to ZMod 2 times ZMod 4, and are not generic APIs. BlockSpliceOrdering requires a supplied injective cycle and exact chord, absent here. IntegerStrongOrdering, attributed there to Kravitz, proves integer existence and does not transform this prescribed compression. Pinned Mathlib supplies list splitting, reversal permutation, prefix sums and finset cardinality. Its AddGroupCone contains zero; StrictCone here states the required strict addition-closed subset instead. No private supplier proof is copied and no literature novelty claim is made.

Escape registration remains unfinished: both exact-telescope Reg families compile their four mathematical slots, but the current report records declared_unresolved with source.selection_missing. The missing original-occurrence source selections are tracked at https://github.com/the-omega-institute/trureturing/issues/21075. They are not claimed declared_validated. Independent source review, required CI and firstfreeze retain their separate scopes.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.ConeLE`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.Good`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.Omega`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.Separated`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.StrictCone`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.compressed`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.expandAt`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.expansion_good`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.expansion_inventory`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.good_iff`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.interior`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.inventory`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.mem_inventory`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.pref`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.pref_append_left`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.pref_append_right`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.reflected`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.reverseBlock`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.same_pair_repair`
- Truth anchor: `D5/S1/Words/Sequenceability/SeparatedPrefixReflection.separated_prefix_reflection`
