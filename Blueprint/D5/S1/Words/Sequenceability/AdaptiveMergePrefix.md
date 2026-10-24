# AdaptiveMergePrefix

## Abstract

For an arbitrary additive commutative group, a word is Good exactly when every nonempty proper contiguous interval has nonzero sum. Equality of prefixes at i < j is permitted only for i = 0 and j = length. The entire word may have sum zero. The prefixSum and ProperIntervals names transparently use SeparatedPrefixReflection.pref and Good. The equivalence directly consumes that original module's good_iff, with no finite-ambient, torsion, nonzero-total, strict-cone or separation assumption. This consumed adapter supplies no new mathematical content.

**Theorem 1.1 (Prefix collisions exactly characterize proper intervals).**

Lean statement: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.good_iff_proper_intervals`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.good_iff_proper_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary additive commutative group, a word is Good exactly when every nonempty proper contiguous interval has nonzero sum. Equality of prefixes at i < j is permitted only for i = 0 and j = length. The entire word may have sum zero. The prefixSum and ProperIntervals names transparently use SeparatedPrefixReflection.pref and Good. The equivalence directly consumes that original module's good_iff, with no finite-ambient, torsion, nonzero-total, strict-cone or separation assumption. This consumed adapter supplies no new mathematical content.

**Theorem 1.2 (An inserted prefix can collide only with a left suffix or right prefix).**

Lean statement: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.bad_expand_implies_collision`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.bad_expand_implies_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding L,(x+y),R adds the single prefix sum sum(L)+x. The original SeparatedPrefixReflection.expansion_good implies by contraposition that a failed expansion inserts a value already in the old inventory. Its mem_inventory supplies an actual old cut; pref_append_left and pref_append_right classify that cut into a left suffix or right prefix. These generic original helpers carry no strict-cone or separation premise. If the compressed word is Good and both x and y are nonzero, failure of L,x,y,R forces a nonempty suffix of L summing to -x or a nonempty prefix of R summing to -y. Both full-word endpoint values remain included in this argument; the existing endpoint equality is not classified as a new defect. This consumed adapter is a one-direction obstruction lemma, used by the four-case fork proof, not a claim that arbitrary compression orders exist.

The unrestricted adaptive principle and original arbitrary-subset parent remain OPEN. Under H and existence of a legal pair for an arbitrary finite nonzero alphabet of size at least three, it remains OPEN whether some actual Good compressed order has a Good adjacent expansion; a complete checked counterexample would refute that principle. Static legal-edge inclusion in ForkEdge does not decide it. The published IntegerStrongOrdering theorem is reused in a transient exact-telescope check; no new integer ordering theorem is retained and concrete ZMod Good is not generalized. No literature novelty claim follows from repository search. Four-slot Reg registration is unfinished; see https://github.com/the-omega-institute/trureturing/issues/21061 for exact targets and missing source-binding evidence.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.bad_expand_implies_collision`
- Truth anchor: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.good_iff_proper_intervals`
- Dependency: [D5/S1/Words/Sequenceability/SeparatedPrefixReflection](SeparatedPrefixReflection.md)
