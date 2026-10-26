# Chosen merge expansion obstruction

## Abstract

A forced internal cut refutes uniform adjacent expansion for a chosen legal merge.

**Definition 1.1 (Proper zero-sum intervals).**

$$Good$$

*Formalization.* `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.Good` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Good(w) requires every nonempty proper contiguous interval of w to have nonzero sum. The whole word is exempt, so a total zero is allowed.

**Definition 1.2 (Adjacent expansion).**

$$expand$$

*Formalization.* `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.expand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

expand x y replaces the unique merged letter x + y by the adjacent pair x,y in a compressed word.

**Definition 1.3 (Guarded universal chosen-merge lifting claim).**

$$claim$$

*Formalization.* `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite A of nonzero group elements with at least three members, and every distinct legal pair a,b whose sum is outside A and nonzero, if the compressed alphabet has a Good permutation then some Good compressed permutation has a Good adjacent expansion in one of the two orientations.

**Theorem 1.4 (Forced-cut refutation in C2 times C4).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In G = ZMod 2 x ZMod 4 choose p=(0,1), q=(0,3), r=(1,0), s=(1,1), t=(1,3), a=(0,2), b=(1,2). For A={p,q,s,t,a,b} and the legal pair (a,b), the compressed alphabet is B={p,q,r,s,t}. The finite forced-cut proof shows that every Good B-order has r in position three and prefix sum b after two entries. Expanding r as a,b creates a proper final zero block of length three; expanding as b,a creates a proper initial zero block of length three. The displayed Good B-order supplies the guard premise. The model and forced-cut classification follow the supplied candidate derivation and completed finite native audit. That audit also checks that A itself has Good order (p,a,t,q,s,b), and that the alternate legal pair (q,s), with q+s=r, succeeds: the Good compressed order (p,a,t,r,b) expands in orientation (q,s) to that A-order. These positive scope facts are native-audit evidence, not additional Lean theorems of this module. Only the every-chosen-pair adjacent lifting route is refuted. The original arbitrary-abelian ordering target and its same-M, original-coordinate, coefficient-one formulation remain OPEN.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.Good`
- Truth anchor: `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.claim`
- Truth anchor: `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.expand`
- Truth anchor: `D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.result`
