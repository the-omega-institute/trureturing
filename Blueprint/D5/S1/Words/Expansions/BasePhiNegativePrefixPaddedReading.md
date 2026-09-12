# Zero-Padded and Finite-Depth Negative Prefixes

## Abstract

Zero padding identifies prefixes 01 and 010, whereas finite-depth occurrences differ exactly at 2, 3, and 4.

**Theorem 1.1 (Appending a forced zero preserves padded occurrence).**

$$\forall (expansion: \operatorname{BasePhiNegativeExpansion}) (w: \operatorname{List} \operatorname{Bool}) (hw: w \neq []) (hlast: w.\operatorname{getLast}(hw) = \mathrm{true}) (N: \operatorname{Nat}),\ \operatorname{PaddedPrefixOccurs}(expansion,w,N) \Leftrightarrow \operatorname{PaddedPrefixOccurs}(expansion,w ++ [\mathrm{false}],N)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.paddedPrefixOccurs_append_false_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every expansion and natural number, a nonempty word ending in true occurs in the zero-padded negative tail exactly when the word with false appended occurs. The last-letter hypothesis forces the following digit to be zero.

**Theorem 1.2 (Padded prefixes 01 and 010 have equal occurrence sets).**

$$\operatorname{paddedOccurrenceSet}(\operatorname{canonicalExpansion},[\mathrm{false},\mathrm{true}]) = \operatorname{paddedOccurrenceSet}(\operatorname{canonicalExpansion},[\mathrm{false},\mathrm{true},\mathrm{false}])$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.paddedOccurrenceSet_prefix01_eq_prefix010` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical zero-padded occurrence sets of 01 and 010 are equal. This establishes only the first equality printed in Proposition 7.8 d) of Dekking's The structure of base phi expansions under the zero-padded reading.

**Theorem 1.3 (Finite-depth occurrence sets differ exactly at 2, 3, and 4).**

$$\operatorname{occurrenceSet}(\operatorname{canonicalExpansion},[\mathrm{false},\mathrm{true}]) \Delta \operatorname{occurrenceSet}(\operatorname{canonicalExpansion},[\mathrm{false},\mathrm{true},\mathrm{false}]) = \{2,3,4\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.occurrenceSet_prefix01_symmDiff_prefix010` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the repository's finite-depth reading, the symmetric difference of the canonical occurrence sets of 01 and 010 is exactly the set containing 2, 3, and 4. These are precisely the exceptions to their equality.

**Theorem 1.4 (The finite-depth equality claim is false).**

$$\neg \left(\operatorname{occurrenceSet}(\operatorname{canonicalExpansion},[\mathrm{false},\mathrm{true}]) = \operatorname{occurrenceSet}(\operatorname{canonicalExpansion},[\mathrm{false},\mathrm{true},\mathrm{false}])\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-depth equality named claim is false; the display unfolds that claim. Thus the first equality in the printed chain holds for the zero-padded reading and fails for the finite-depth reading.

**Theorem 1.5 (Two belongs to the padded core of 010).**

$$2 \in \operatorname{PaddedCore}([\mathrm{false},\mathrm{true},\mathrm{false}])$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.two_mem_paddedCore010` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number 2 is a fiber start whose canonical zero-padded negative tail begins with 010, so it belongs to the padded core of that word.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.occurrenceSet_prefix01_symmDiff_prefix010`
- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.paddedOccurrenceSet_prefix01_eq_prefix010`
- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.paddedPrefixOccurs_append_false_iff`
- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.result`
- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.two_mem_paddedCore010`
