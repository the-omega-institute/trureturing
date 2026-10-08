# Circular Deletion Transport

## Abstract

An oriented circular word with no repeated initial labels cannot reverse by deleting and reinserting labels while three initial labels remain untouched.

An oriented circular word is a finite list modulo rotation, using the native Cycle carrier. The quotient identifies rotations; it does not additionally identify reversal. Restriction filters a chosen set of labels before taking the rotation class. Deleting x is restriction to labels different from x. A deletion step between C and D requires that deleting x from both gives exactly the same oriented residual circle. DeleteWalk records a finite sequence of these steps and its omission word xs; repeated omissions and omissions outside the initial support are allowed.

**Theorem 1.1 (Untouched Circular Restrictions Are Preserved).**

$$\forall A \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(A\right)] \forall xs \in \mathrm{List}\left(A\right),\; \forall C \in \mathrm{Cycle}\left(A\right),\; \forall D \in \mathrm{Cycle}\left(A\right),\; \forall p \in A \to \mathrm{Bool},\; (\mathrm{DeleteWalk}\left(xs, C, D\right)) \Rightarrow ((\forall x \in A,\; (x \in xs) \Rightarrow (p\left(x\right) = \mathrm{false})) \Rightarrow (\mathrm{restrict}\left(p, C\right) = \mathrm{restrict}\left(p, D\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean predicate p that excludes every omitted label, restriction to p is the same at both ends of a deletion walk. Filtering commutes with rotation, so restriction is independent of the chosen list representative. If p excludes x, filtering after deleting x equals filtering directly. Applying that equality to each deletion step and composing along the walk proves preservation.

**Theorem 1.2 (Negative Transport Omits All but Two Initial Labels).**

$$\forall A \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(A\right)] \forall xs \in \mathrm{List}\left(A\right),\; \forall C \in \mathrm{Cycle}\left(A\right),\; (\mathrm{DeleteWalk}\left(xs, C, \mathrm{reverse}\left(C\right)\right)) \Rightarrow ((\mathrm{Nodup}\left(C\right)) \Rightarrow (\mathrm{card}\left(\mathrm{toFinset}\left(C\right)\right) \le \mathrm{card}\left(\mathrm{toFinset}\left(xs\right)\right) + 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.negative_walk_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C have no repeated labels. If a deletion walk ends at C.reverse, the number of distinct initial labels is at most the number of distinct omitted labels plus two. Three untouched initial labels would retain their circular restriction throughout the walk. That restriction has exactly three distinct labels, so its orientation differs from its reverse. This contradicts the negative endpoint. Counting the untouched support gives the bound. The ambient label type may be infinite, and intermediate circles need not have the initial support.

If C has no repeated labels and contains all n labels, the bound gives at least n minus two distinct omissions. Its use for a whole-supplier incidence requires an actual equality of oriented deletion residuals at that incidence. Equality after also identifying reversal is insufficient. This result neither constructs a Hamilton cycle nor establishes a boundary-preserving supplier lift.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.negative_walk_support_bound`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.restrict_walk`
