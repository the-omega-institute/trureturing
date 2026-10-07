# Finite Height Normalization for Labelled Prefix Covers

## Abstract

A finite labelled cover by prefix cylinders can be shortened to a depth bounded by its surviving number of members and the target's fixed prefix length.

Let the alphabet, index type, label type and side-coordinate type be arbitrary types. Fix an alphabet element a and a natural number r. A stream is a function from the natural numbers to the alphabet. Prefix(k,x,w) means x(t)=w(t) for every t<k. An indexed cover consists of a finite index set I, positive depths h(i)>r, reference streams w(i), labels c(i), and side predicates T(i,z). The target predicate E(x,z) depends on x only through its first r symbols: agreement there transports membership in E. Covers(I,h,w,T,E) means that every point of E satisfies Prefix(h(i),x,w(i)) and T(i,z) for some i in I. DistinctLabels means that the pairs (h(i),c(i)) are injective on I; the label c(i) alone may repeat at different depths.

**Theorem 1.1 (A Bound by the Number of Surviving Members).**

$$\forall I \in \mathrm{Finset}\left(Index\right),\; \forall h \in \mathrm{Function}\left(Index, Nat\right),\; \forall w \in \mathrm{Function}\left(Index, Stream\right),\; \forall c \in \mathrm{Function}\left(Index, Label\right),\; \forall T \in \mathrm{SidePredicates}\left(Index, Side\right),\; \forall E \in \mathrm{TargetPredicate}\left(Stream, Side\right),\; \forall r \in Nat,\; \forall a \in Alphabet,\; (\mathrm{TargetDependsOnPrefix}\left(E, r\right) \land \left(\mathrm{DepthsAbove}\left(I, h, r\right) \land \left(\mathrm{DistinctLabels}\left(I, h, c\right) \land \mathrm{Covers}\left(I, h, w, T, E\right)\right)\right)) \Rightarrow (\exists J \in \mathrm{Finset}\left(Index\right),\; \exists hnew \in \mathrm{Function}\left(Index, Nat\right),\; \exists wnew \in \mathrm{Function}\left(Index, Stream\right),\; \mathrm{Subset}\left(J, I\right) \land \left(\mathrm{PointwiseDepthBoundsAndOldPrefixAgreement}\left(J, hnew, wnew, h, w, r\right) \land \left(\mathrm{DistinctLabels}\left(J, hnew, c\right) \land \mathrm{Covers}\left(J, hnew, wnew, T, E\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PrefixCovers/HeightNormalization.normalize_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under these hypotheses there are J contained in I, new depths h' and new streams w' such that every i in J satisfies r<h'(i)<=r+|J| and h'(i)<=h(i), and w'(i) agrees with w(i) on its first r symbols. The pairs (h'(i),c(i)) remain injective on J, and the cylinders still cover the same E with the original side predicates T. Thus the side coordinate, its permitted sets, and the old prefix symbols are preserved. No finiteness assumption is imposed on the alphabet or on the side-coordinate type. Empty index sets and empty targets are allowed when the coverage premise holds.

If some used depth K exceeds r+|I|, cardinality of the integer interval from r+1 through K yields an unused depth g. Insert the fixed symbol a at stream position g-1 and take inverse images of the original covering cylinders. Depths below g are unchanged. A cylinder of depth above g disappears when its prescribed symbol at g-1 is not a; otherwise it shortens by one and deletes that symbol from its reference stream. The target is unchanged under this inverse image because g-1>=r. There was no cylinder at depth g, so shortened and unchanged height-label pairs cannot collide. The sum of all retained depths strictly decreases, giving a terminating induction.

For any nonnegative per-member costs that are nondecreasing with depth, the resulting total cost does not increase: retained depths decrease and removed members contribute nothing. With r=2 and at most M original members, every surviving depth is at most M+2. This is a conditional normalization of an existing prefix cover. It neither constructs a cover from fractional data nor proves that a congruence system has such a replacement. Applying it to arithmetic progressions requires a separate coordinate correspondence and a proof that numerical label distinctness is equivalent to the stated pair condition.

## References

- Truth anchor: `D5/S3/Combinatorics/PrefixCovers/HeightNormalization.normalize_cover`
