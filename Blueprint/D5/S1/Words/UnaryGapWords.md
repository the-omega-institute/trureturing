# Unary Gaps of Actual Words

## Abstract

Occurrence-indexed unary gaps and complete positional source traces.

Fix a letter a in an arbitrary alphabet. A gap word alternates blocks of a with a list of non-a occurrences. The list preserves repeated letters as separate occurrences. Its gap vector has one more entry than its occurrence list; entries may be zero.

**Definition 1.1 (Gap concatenation).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \operatorname{gap}\left(a, cs, h\right) : \operatorname{List}\left(alpha\right)$$

*Formalization.* `D5/S1/Words/UnaryGapWords.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an empty occurrence list, take the first gap's copies of a. For c followed by cs, concatenate the first a block, c, and the remaining gap word. All uses of a gap presentation supply exactly one more mass than occurrences.

**Definition 1.2 (Non-a occurrences).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall w \in \operatorname{List}\left(alpha\right),\; \operatorname{spine}\left(a, w\right) = \operatorname{filter}\left(notEqualToA, w\right)$$

*Formalization.* `D5/S1/Words/UnaryGapWords.spine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the actual word by inequality to a without removing multiplicities.

**Definition 1.3 (Canonical gap lengths).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall w \in \operatorname{List}\left(alpha\right),\; \operatorname{sizes}\left(a, w\right) : \operatorname{List}\left(\operatorname{Nat}\left(\right)\right)$$

*Formalization.* `D5/S1/Words/UnaryGapWords.sizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scan from the right. An a increments the first gap; a non-a occurrence starts a new zero gap. The empty word has the single gap zero.

**Theorem 1.4 (Uniqueness of indexed gap words).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall ds \in \operatorname{List}\left(alpha\right),\; \forall k \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \left(\left(\forall x \in alpha,\; x \in ds \Rightarrow x \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \operatorname{length}\left(k\right) = \operatorname{length}\left(ds\right) + 1\right)\right)\right) \Rightarrow \left(\operatorname{gap}\left(a, cs, h\right) = \operatorname{gap}\left(a, ds, k\right) \Rightarrow \left(cs = ds \land h = k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.gap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Recovering the spine and lengths from each actual concatenation proves both equalities, including repeated separators and zero gaps.

**Theorem 1.5 (Every word has a canonical presentation).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall w \in \operatorname{List}\left(alpha\right),\; \exists cs \in \operatorname{List}\left(alpha\right),\; \exists h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land w = \operatorname{gap}\left(a, cs, h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.gap_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical spine and gap lengths reconstruct the original word.

**Definition 1.6 (Complete gap labels).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall q \in Side,\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \operatorname{Trace}\left(a, q, cs, h, e, w, M\right) : \operatorname{Prop}\left(\right)$$

*Formalization.* `D5/S1/Words/UnaryGapWords.Trace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every a gap retains its whole label list b. Its q count contributes to h, and its opposite-source count contributes to e. Every non-a occurrence has label q. This is an inductive decomposition of actual letters and labels.

**Definition 1.7 (Grouped labels in each gap).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall q \in Side,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \operatorname{grouped}\left(q, cs, h, e\right) : \operatorname{List}\left(Side\right)$$

*Formalization.* `D5/S1/Words/UnaryGapWords.grouped` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With a unary inserted source, place its gap mass together after the base copies. With a unary base source, place base copies before the inserted copies in each nonterminal gap, and after them in the terminal gap.

**Theorem 1.8 (Unique extra masses and actual masks).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall q \in Side,\; \forall m \in \operatorname{Nat}\left(\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \left(\left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1\right) \Rightarrow \left(\left(\exists M \in \operatorname{List}\left(Side\right),\; \operatorname{length}\left(M\right) = \operatorname{length}\left(w\right) \land \left(\operatorname{projection}\left(q, w, M\right) = \operatorname{gap}\left(a, cs, h\right) \land \operatorname{projection}\left(\operatorname{opposite}\left(q\right), w, M\right) = \operatorname{replicate}\left(m, a\right)\right)\right) \Leftrightarrow \left(\exists e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{sum}\left(e\right) = m \land w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right)\right) \land \left(\forall f \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\operatorname{length}\left(f\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{sum}\left(f\right) = m \land w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, f\right)\right)\right)\right) \Rightarrow f = e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.native_gap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each native projection pair, non-a letters are forced to q. Splitting at those occurrences gives every label gap and both projected words. Conversely, grouped gap labels realize every permitted mass vector. Canonical word recovery makes the extra vector unique. No alphabet order, decidable equality premise or distinctness between separators is assumed.

**Theorem 1.9 (Canonical recovery of a presented gap word).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1\right) \Rightarrow \left(\operatorname{spine}\left(a, \operatorname{gap}\left(a, cs, h\right)\right) = cs \land \operatorname{sizes}\left(a, \operatorname{gap}\left(a, cs, h\right)\right) = h\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.profile_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filtering recovers exactly the occurrence list, and the canonical gap scan recovers exactly the supplied lengths.

**Theorem 1.10 (Both projections of a positional trace).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall q \in Side,\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \operatorname{Trace}\left(a, q, cs, h, e, w, M\right) \Rightarrow \left(\operatorname{length}\left(M\right) = \operatorname{length}\left(w\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \left(\left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \left(\operatorname{projection}\left(q, w, M\right) = \operatorname{gap}\left(a, cs, h\right) \land \left(\operatorname{projection}\left(\operatorname{opposite}\left(q\right), w, M\right) = \operatorname{replicate}\left(\operatorname{sum}\left(e\right), a\right) \land w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.trace_projections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace gives matching word and mask lengths, both ordered source projections, all vector lengths and the actual enlarged gap word.

**Theorem 1.11 (Extracting the full trace).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall q \in Side,\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \left(\operatorname{length}\left(M\right) = \operatorname{length}\left(w\right) \land \left(\forall x \in alpha,\; x \in \operatorname{projection}\left(\operatorname{opposite}\left(q\right), w, M\right) \Rightarrow x = a\right)\right) \Rightarrow \left(\exists cs \in \operatorname{List}\left(alpha\right),\; \exists h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \exists e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \operatorname{Trace}\left(a, q, cs, h, e, w, M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.trace_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each non-a occurrence the opposite projection excludes its label. Splitting there retains every intervening label and all zero gaps.

**Theorem 1.12 (Realizing every extra vector).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall q \in Side,\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \left(\left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \operatorname{length}\left(e\right) = \operatorname{length}\left(h\right)\right)\right) \Rightarrow \operatorname{Trace}\left(a, q, cs, h, e, \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right), \operatorname{grouped}\left(q, cs, h, e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.trace_construct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The grouped mask realizes each permitted vector on an actual gap word, including the no-separator case and both exterior masses.

**Theorem 1.13 (Recovering prescribed gap masses).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall q \in Side,\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall w \in \operatorname{List}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \left(\left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \left(w = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right) \land \left(\operatorname{length}\left(M\right) = \operatorname{length}\left(w\right) \land \left(\operatorname{projection}\left(q, w, M\right) = \operatorname{gap}\left(a, cs, h\right) \land \left(\forall x \in alpha,\; x \in \operatorname{projection}\left(\operatorname{opposite}\left(q\right), w, M\right) \Rightarrow x = a\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Trace}\left(a, q, cs, h, e, w, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.trace_of_projections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual word uniqueness identifies the extracted original and extra gaps with their prescribed vectors, without identifying repeated separators.

**Theorem 1.14 (Transport at an actual word cut).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall a \in alpha,\; \forall cs \in \operatorname{List}\left(alpha\right),\; \forall h \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall e \in \operatorname{List}\left(\operatorname{Nat}\left(\right)\right),\; \forall X \in \operatorname{List}\left(alpha\right),\; \forall Y \in \operatorname{List}\left(alpha\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \left(\left(\forall x \in alpha,\; x \in cs \Rightarrow x \ne a\right) \land \left(\operatorname{length}\left(h\right) = \operatorname{length}\left(cs\right) + 1 \land \left(\operatorname{length}\left(e\right) = \operatorname{length}\left(h\right) \land \operatorname{append}\left(X, Y\right) = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, e\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{length}\left(\operatorname{spine}\left(a, X\right)\right) < \operatorname{length}\left(e\right) \land \left(\operatorname{length}\left(\operatorname{modify}\left(e, \operatorname{length}\left(\operatorname{spine}\left(a, X\right)\right), \operatorname{add}\left(k\right)\right)\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{sum}\left(\operatorname{modify}\left(e, \operatorname{length}\left(\operatorname{spine}\left(a, X\right)\right), \operatorname{add}\left(k\right)\right)\right) = \operatorname{sum}\left(e\right) + k \land \operatorname{append}\left(\operatorname{append}\left(X, \operatorname{replicate}\left(k, a\right)\right), Y\right) = \operatorname{gap}\left(a, cs, \operatorname{zipWith}\left(add, h, \operatorname{modify}\left(e, \operatorname{length}\left(\operatorname{spine}\left(a, X\right)\right), \operatorname{add}\left(k\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/UnaryGapWords.gap_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let i count the non-a occurrences in X. Then i is a valid gap index. Inserting k copies of a at X|Y adds k only to e[i], preserves vector length, increases its sum by k, and gives exactly the concatenated word X followed by a^k followed by Y. This is an identity on actual words.

## References

- Truth anchor: `D5/S1/Words/UnaryGapWords.Trace`
- Truth anchor: `D5/S1/Words/UnaryGapWords.gap`
- Truth anchor: `D5/S1/Words/UnaryGapWords.gap_exists`
- Truth anchor: `D5/S1/Words/UnaryGapWords.gap_injective`
- Truth anchor: `D5/S1/Words/UnaryGapWords.gap_insert`
- Truth anchor: `D5/S1/Words/UnaryGapWords.grouped`
- Truth anchor: `D5/S1/Words/UnaryGapWords.native_gap_iff`
- Truth anchor: `D5/S1/Words/UnaryGapWords.profile_gap`
- Truth anchor: `D5/S1/Words/UnaryGapWords.sizes`
- Truth anchor: `D5/S1/Words/UnaryGapWords.spine`
- Truth anchor: `D5/S1/Words/UnaryGapWords.trace_construct`
- Truth anchor: `D5/S1/Words/UnaryGapWords.trace_exists`
- Truth anchor: `D5/S1/Words/UnaryGapWords.trace_of_projections`
- Truth anchor: `D5/S1/Words/UnaryGapWords.trace_projections`
- Dependency: [D5/S1/Words/HughesBlockExchange](HughesBlockExchange.md)
