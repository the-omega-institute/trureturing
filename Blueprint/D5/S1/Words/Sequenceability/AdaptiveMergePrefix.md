# AdaptiveMergePrefix

## Abstract

For an arbitrary additive commutative group, a word is Good exactly when every nonempty proper contiguous interval has nonzero sum. Equality of prefixes at i < j is permitted only for i = 0 and j = length. The entire word may have sum zero. The proof uses the public List.sum_take_add_sum_drop and List.drop_take APIs with no finite-ambient, torsion or nonzero-total assumption.

**Theorem 1.1 (Prefix collisions exactly characterize proper intervals).**

Lean statement: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.good_iff_proper_intervals`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.good_iff_proper_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary additive commutative group, a word is Good exactly when every nonempty proper contiguous interval has nonzero sum. Equality of prefixes at i < j is permitted only for i = 0 and j = length. The entire word may have sum zero. The proof uses the public List.sum_take_add_sum_drop and List.drop_take APIs with no finite-ambient, torsion or nonzero-total assumption.

**Theorem 1.2 (An inserted prefix can collide only with a left suffix or right prefix).**

Lean statement: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.bad_expand_implies_collision`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.bad_expand_implies_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding L,(x+y),R adds the single prefix sum sum(L)+x. Every other prefix has the old compressed value at oldCut, an injective map away from the inserted cut. If the compressed word is Good and both x and y are nonzero, failure of L,x,y,R forces a nonempty suffix of L summing to -x or a nonempty prefix of R summing to -y. Both full-word endpoint values remain included in this argument; the existing endpoint equality is not classified as a new defect. This is a one-direction obstruction lemma, consumed by the four-case fork proof, not a claim that arbitrary compression orders exist.

The unrestricted adaptive principle and original arbitrary-subset parent remain OPEN. Under H and existence of a legal pair for an arbitrary finite nonzero alphabet of size at least three, it remains OPEN whether some actual Good compressed order has a Good adjacent expansion; a complete checked counterexample would refute that principle. Static legal-edge inclusion in ForkEdge does not decide it. The published IntegerStrongOrdering theorem is reused in a transient exact-telescope check; no new integer ordering theorem is retained and concrete ZMod Good is not generalized. No literature novelty claim follows from repository search. Four-slot Reg registration is unfinished; see https://github.com/the-omega-institute/trureturing/issues/21061 for exact targets and missing source-binding evidence.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.bad_expand_implies_collision`
- Truth anchor: `D5/S1/Words/Sequenceability/AdaptiveMergePrefix.good_iff_proper_intervals`
