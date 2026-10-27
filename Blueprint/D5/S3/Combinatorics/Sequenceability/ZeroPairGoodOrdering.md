# A zero pair and its original complement

## Abstract

A zero pair and its original complement

**Theorem 1.1 (A full Good order from a zero pair).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering.exists_good_order_of_zero_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering.exists_good_order_of_zero_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type is arbitrary, X is finite, and a is injective with nonzero original labels. For distinct s,t in X with a(s)+a(t)=0, assume only that the complement C has no nonempty zero subset. There is a permutation of every original index in X whose mapped word is Good. Good excludes zero sums on every nonempty proper consecutive subword; the full total is arbitrary.

The consumed two-prefix construction orders distinct labels of total T while avoiding f,g on nonempty proper prefixes when at least one of T-f,T-g is absent. With two remaining choices, simultaneous failure forces exactly those two labels. For T different from both pair labels, use (s,C,t), with prefix exclusions -a(s),T-a(s). At T=a(s), derive a choice c in C with a(c) different from 2a(s), order D=C minus c avoiding 2a(s),2a(s)-a(c), and use (t,D,s,c). Swap s,t for the other exceptional total. Empty and singleton complements remain in the theorem's scope.

**Theorem 1.2 (Exact integer extraction from full coverage).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering.full_blocker_pair_extract`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering.full_blocker_pair_extract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H covers every permutation of the finite original index type by a nonempty proper interval. Its span is exactly the integer span of its original Boolean rows. If the row of a distinct pair belongs to that span, then it contains an original unit, an original difference, or a nonempty Boolean row supported off that pair. The last alternative includes an actual integer coefficient function on H whose sum equals the extracted row.

The consumer takes the exact quotient by the integer row span. Absence of original primitives makes the original quotient labels injective and nonzero. If there were no complementary Boolean zero row, the Good construction would contradict full coverage. Quotient zero is equivalent to exact integer span membership; Submodule.mem_span_range_iff_exists_fun recovers integer coefficients. There is no division, saturation or passage from a nonzero multiple to a primitive.

This construction follows the completed native zero-pair argument as fallible input and reuses PairedZeroSubsetSpectrum.Good and SeparatedPrefixReflection.good_iff. The greedy lemma and the finite order construction supply the new inference; normalization and span witness recovery are consumed helpers. The extracted subset may equal all of C and may be absent from H. No inherited every-permutation blocker on C, smaller minimum zero size, or solution of the unrestricted Good/exact integral blocker target follows. Literature novelty is not claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering.exists_good_order_of_zero_pair`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering.full_blocker_pair_extract`
- Dependency: [D5/S1/Words/Sequenceability/SeparatedPrefixReflection](../../../S1/Words/Sequenceability/SeparatedPrefixReflection.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum](PairedZeroSubsetSpectrum.md)
