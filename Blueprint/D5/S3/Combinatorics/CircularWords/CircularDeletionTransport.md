# Circular Deletion Transport

## Abstract

An oriented circular word with no repeated initial labels cannot reverse by deleting and reinserting labels while three initial labels remain untouched.

An oriented circular word is a finite list modulo rotation, using the native Cycle carrier. The quotient identifies rotations; it does not additionally identify reversal. Restriction filters a chosen set of labels before taking the rotation class. Deleting x is restriction to labels different from x. A deletion step between C and D requires that deleting x from both gives exactly the same oriented residual circle. DeleteWalk records a finite sequence of these steps and its omission word xs; repeated omissions and omissions outside the initial support are allowed.

**Lemma 1.1 (Restriction Commutes with Reversal).**

$$\forall A \in \mathrm{Type},\; \forall p \in A \to \mathrm{Bool},\; \forall C \in \mathrm{Cycle}\left(A\right),\; \mathrm{restrict}\left(p, \mathrm{reverse}\left(C\right)\right) = \mathrm{reverse}\left(\mathrm{restrict}\left(p, C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every label type A, Boolean predicate p and oriented circle C, restricting reverse(C) equals reversing restrict(p,C). Choose a list representative of C. Filtering its reversal equals reversing its filtered list, and this equality descends to the rotation quotient. The label type may be infinite; the theorem requires no equality decision on A.

**Lemma 1.2 (Successive Restrictions Compose).**

$$\forall A \in \mathrm{Type},\; \forall p \in A \to \mathrm{Bool},\; \forall q \in A \to \mathrm{Bool},\; \forall C \in \mathrm{Cycle}\left(A\right),\; \mathrm{restrict}\left(p, \mathrm{restrict}\left(q, C\right)\right) = \mathrm{restrict}\left((y \mapsto \mathrm{BoolAnd}\left(p\left(y\right), q\left(y\right)\right)), C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every label type A, Boolean predicates p and q and oriented circle C, restriction by q followed by p is restriction by the Boolean conjunction of their values. BoolAnd in the displayed formula denotes Lean's Boolean conjunction, and the arrow expression denotes a function of y. Choose a list representative of C. Filtering it twice equals filtering once by that Boolean conjunction, and the equality descends to the rotation quotient.

**Theorem 1.3 (Untouched Circular Restrictions Are Preserved).**

$$\forall A \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(A\right)] \forall xs \in \mathrm{List}\left(A\right),\; \forall C \in \mathrm{Cycle}\left(A\right),\; \forall D \in \mathrm{Cycle}\left(A\right),\; \forall p \in A \to \mathrm{Bool},\; (\mathrm{DeleteWalk}\left(xs, C, D\right)) \Rightarrow ((\forall x \in A,\; (x \in xs) \Rightarrow (p\left(x\right) = \mathrm{false})) \Rightarrow (\mathrm{restrict}\left(p, C\right) = \mathrm{restrict}\left(p, D\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean predicate p that excludes every omitted label, restriction to p is the same at both ends of a deletion walk. Filtering commutes with rotation, so restriction is independent of the chosen list representative. If p excludes x, filtering after deleting x equals filtering directly. Applying that equality to each deletion step and composing along the walk proves preservation.

**Theorem 1.4 (Negative Transport Omits All but Two Initial Labels).**

$$\forall A \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(A\right)] \forall xs \in \mathrm{List}\left(A\right),\; \forall C \in \mathrm{Cycle}\left(A\right),\; (\mathrm{DeleteWalk}\left(xs, C, \mathrm{reverse}\left(C\right)\right)) \Rightarrow ((\mathrm{Nodup}\left(C\right)) \Rightarrow (\mathrm{card}\left(\mathrm{toFinset}\left(C\right)\right) \le \mathrm{card}\left(\mathrm{toFinset}\left(xs\right)\right) + 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.negative_walk_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C have no repeated labels. If a deletion walk ends at C.reverse, the number of distinct initial labels is at most the number of distinct omitted labels plus two. Three untouched initial labels would retain their circular restriction throughout the walk. That restriction has exactly three distinct labels, so its orientation differs from its reverse. This contradicts the negative endpoint. Counting the untouched support gives the bound. The ambient label type may be infinite, and intermediate circles need not have the initial support.

Every readout that factors through an untouched restriction inherits this invariant: if r(C)=h(restrict(p,C)) and p excludes every label in xs, restrict_walk gives r(C)=r(D) at the two ends of DeleteWalk(xs,C,D). The factor h may have any output type. This supplies a concrete readout invariant without introducing a state-record or trajectory structure.

DeleteWalk is a relation of legal deletion/reinsertion incidences, not a selected controlled update. For example C=[0,1,2] and D=[0,2,1] are distinct oriented rotation classes, but deleting 0 gives the same two-label residual. Thus both DeleteWalk([0],C,C) and DeleteWalk([0],C,D) hold. The same source and omitted label therefore admit different successors. The definition supplies neither a canonical deterministic choice of successor nor an append operation or certified history observation. A separately specified controller may choose a successor and a separately specified history may record it; the relational interface alone does not supply those extra data or their laws.

If C has no repeated labels and contains all n labels, the bound gives at least n minus two distinct omissions. Its use for a whole-supplier incidence requires an actual equality of oriented deletion residuals at that incidence. Equality after also identifying reversal is insufficient. This result neither constructs a Hamilton cycle nor establishes a boundary-preserving supplier lift.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.negative_walk_support_bound`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_restrict`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_reverse`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_walk`
