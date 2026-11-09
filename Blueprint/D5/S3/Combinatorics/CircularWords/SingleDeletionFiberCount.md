# Exact Single-Deletion Fibre Count

## Abstract

A fixed-support oriented cycle has exactly one legal source for each insertion gap, so a labelled single-deletion fibre has cardinality A.card - 1.

Let A be a finite support in an arbitrary ambient type with decidable equality. The carrier is the native Mathlib Cycle quotient: rotation classes are identified and reversal remains distinct. Fix x in A and a nodup residual cycle B whose support is A.erase x. The fibre consists of actual original cycles C with C.Nodup, C.toFinset = A, and the labelled deletion delete x C equal to B.

**Theorem 1.1 (Insertion Slots Are the Exact Fibre).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall x \in T,\; \forall B \in \mathrm{List}\left(T\right),\; ((x \in A) \land ((\mathrm{Nodup}\left(B\right)) \land ((\neg (B = \mathrm{nil})) \land (\mathrm{toFinset}\left(B\right) = \mathrm{erase}\left(x, A\right))))) \Rightarrow (\mathrm{Equiv}\left(\mathrm{Fin}\left(\mathrm{length}\left(B\right)\right), \mathrm{Subtype}\left((\mathrm{Nodup}\left(C\right)) \land ((\mathrm{toFinset}\left(C\right) = A) \land (\mathrm{delete}\left(x, C\right) = \mathrm{coeCycle}\left(B\right)))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/SingleDeletionFiberCount.insertionEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose any nodup list representative L of B. For j in Fin L.length, gapCircle L x j inserts x immediately before the jth residual entry after rotating L; j = 0 is the cyclic cut before L[0]. Every displayed cycle is nodup, has exactly support A, and deletes to B. The existing gapCircle_fiber theorem supplies a unique slot for every legal source cycle. Anchored injectivity together with nodup rotation uniqueness proves that two slots cannot give the same rotation class, so the equivalence counts actual cycles rather than chosen representatives.

**Theorem 1.2 (The Fibre Has Cardinality A.card Minus One).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall x \in T,\; \forall B \in \mathrm{Cycle}\left(T\right),\; ((3 \le \mathrm{card}\left(A\right)) \land ((x \in A) \land ((\mathrm{Nodup}\left(B\right)) \land (\mathrm{toFinset}\left(B\right) = \mathrm{erase}\left(x, A\right))))) \Rightarrow (\mathrm{NatCard}\left(\mathrm{Subtype}\left((\mathrm{Nodup}\left(C\right)) \land ((\mathrm{toFinset}\left(C\right) = A) \land (\mathrm{delete}\left(x, C\right) = B))\right)\right) = \mathrm{card}\left(A\right) - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/SingleDeletionFiberCount.deletion_fiber_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a residual cycle B supported on A.erase x, choose a representative L. Nodup support gives L.length = (A.erase x).card = A.card - 1. Transporting Nat.card across insertionEquiv therefore yields the exact cardinality of the subtype of original rotation classes. The statement is valid for every ambient type; it assumes no Fintype α and makes no probability, enumeration, optimum, or novelty claim.

The fibre includes every insertion slot, including the wrap-around cut, and keeps the source support and orientation exact. A transient SupportedCircle application can use the same equivalence, but the canonical result is the two reusable declarations above.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/SingleDeletionFiberCount.deletion_fiber_card`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/SingleDeletionFiberCount.insertionEquiv`
- Dependency: [D5/S3/Combinatorics/CircularWords/CyclicInsertionGap](CyclicInsertionGap.md)
