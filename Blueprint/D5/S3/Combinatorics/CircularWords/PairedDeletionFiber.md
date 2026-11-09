# Paired Circular Deletion Fibres

## Abstract

For a fixed support of at least three labels, a pair of labelled circular deletions has a fibre of at most two: the source circle and, exactly when the deleted labels are adjacent, its adjacent swap.

Fix a finite support A and nodup oriented circles C,D with toFinset C = toFinset D = A. For distinct support labels a,b, the labelled observations are the two residual circles delete a C and delete b C. Choose one marker r in A minus {a,b}; rooting both rotation classes at r turns residual equality into equality of two anchored filtered lists.

**Theorem 1.1 (Necessary and sufficient classification).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall a \in T,\; \forall b \in T,\; \forall C \in \mathrm{Cycle}\left(T\right),\; \forall D \in \mathrm{Cycle}\left(T\right),\; ((3 \le \mathrm{card}\left(A\right)) \land ((a \in A) \land ((b \in A) \land ((\neg (a = b)) \land (((\mathrm{Nodup}\left(C\right)) \land (\mathrm{toFinset}\left(C\right) = A)) \land ((\mathrm{Nodup}\left(D\right)) \land (\mathrm{toFinset}\left(D\right) = A))))))) \Rightarrow (((\mathrm{delete}\left(a, C\right) = \mathrm{delete}\left(a, D\right)) \land (\mathrm{delete}\left(b, C\right) = \mathrm{delete}\left(b, D\right))) \Leftrightarrow ((C = D) \lor (\exists r \in T,\; (r \in A) \land ((\neg (r = a)) \land ((\neg (r = b)) \land (\mathrm{adjacentSwapAt}\left(r, a, b, C, D\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PairedDeletionFiber.paired_fiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The list proof is induction on the first nodup list. If both heads lie outside {a,b}, either erasure preserves the heads, forcing equal heads and a recursive tail classification. Equal a or b heads are fixed by the other erasure and nodup. Opposite heads force the tails to be b::R and a::R (or the symmetric form), so the full words differ exactly by an adjacent a,b swap. Rooted equality is converted with anchored_coe_injective, and the converse is the direct filter calculation.

**Theorem 1.2 (At most two states in one fibre).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall a \in T,\; \forall b \in T,\; \forall C \in \mathrm{Cycle}\left(T\right),\; \forall D \in \mathrm{Cycle}\left(T\right),\; \forall E \in \mathrm{Cycle}\left(T\right),\; ((3 \le \mathrm{card}\left(A\right)) \land ((a \in A) \land ((b \in A) \land ((\neg (a = b)) \land (((\mathrm{Nodup}\left(C\right)) \land (\mathrm{toFinset}\left(C\right) = A)) \land (((\mathrm{Nodup}\left(D\right)) \land (\mathrm{toFinset}\left(D\right) = A)) \land (((\mathrm{Nodup}\left(E\right)) \land (\mathrm{toFinset}\left(E\right) = A)) \land (((\mathrm{delete}\left(a, C\right) = \mathrm{delete}\left(a, D\right)) \land (\mathrm{delete}\left(b, C\right) = \mathrm{delete}\left(b, D\right))) \land (((\mathrm{delete}\left(a, C\right) = \mathrm{delete}\left(a, E\right)) \land (\mathrm{delete}\left(b, C\right) = \mathrm{delete}\left(b, E\right))) \land ((\neg (D = C)) \land (\neg (E = C)))))))))))) \Rightarrow (D = E)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PairedDeletionFiber.pair_fiber_at_most_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose one marker r outside the deleted pair and use it for C,D,E. The fixed-root classification makes every non-central fibre member the swap map of C by the same Equiv.swap a b. Hence two members different from C are equal. The result is stated for card A >= 3, which is the exact scope needed to choose the common root.

**Theorem 1.3 (A nontrivial alternative exists exactly at a cyclic adjacent cut).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall a \in T,\; \forall b \in T,\; \forall C \in \mathrm{Cycle}\left(T\right),\; ((3 \le \mathrm{card}\left(A\right)) \land ((a \in A) \land ((b \in A) \land ((\neg (a = b)) \land ((\mathrm{Nodup}\left(C\right)) \land (\mathrm{toFinset}\left(C\right) = A)))))) \Rightarrow ((\exists D \in \mathrm{Cycle}\left(T\right),\; (\mathrm{Nodup}\left(D\right)) \land ((\mathrm{toFinset}\left(D\right) = A) \land ((\neg (D = C)) \land ((\mathrm{delete}\left(a, C\right) = \mathrm{delete}\left(a, D\right)) \land (\mathrm{delete}\left(b, C\right) = \mathrm{delete}\left(b, D\right)))))) \Leftrightarrow (\exists r \in T,\; (r \in A) \land ((\neg (r = a)) \land ((\neg (r = b)) \land (\mathrm{cyclicAdjacentAt}\left(r, a, b, C\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PairedDeletionFiber.exists_nontrivial_alternative_iff_cyclicAdjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a supported nodup source circle, an actual second supported circle with the same two labelled deletions and different rotation class exists exactly when the two deleted labels occupy a cyclically adjacent pair. The witness includes every rooted cut, including the wrap-around cut: the source is r::P++[a,b]++Q or r::P++[b,a]++Q, and the constructed alternative reverses that adjacent block. The proof preserves nodup by the adjacent list permutation, support by the same permutation, proves both filtered deletion equalities, and rules out equality by anchored injectivity and a≠b.

The carrier identifies rotations and preserves orientation. The observations are paired residuals from the same source cycle. The statements concern exact finite objects; they make no marginal-law, noise-stability, or sample-complexity assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionFiber.exists_nontrivial_alternative_iff_cyclicAdjacent`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionFiber.pair_fiber_at_most_two`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionFiber.paired_fiber_iff`
- Dependency: [D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction](DeletionReadoutReconstruction.md)
