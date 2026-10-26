# The invariant obstruction of a retained LARGE skeleton

## Abstract

Construct an order of every complete SMALL batch from the prescribed endpoints and both sides of every retained LARGE occurrence.

**Theorem 1.1 (Reconstruct all intervening SMALL batches).**

Lean statement: `D5/S3/Combinatorics/Circle/LargeSkeletonOrdering.exists_order_preserving_large`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/LargeSkeletonOrdering.exists_order_preserving_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let physical labels have arbitrary integer weights f. Fix a positive integer Q and a capacity C with 2Q-2<=C; in particular C=2Q-1 is allowed. SMALL means abs(f(i))<Q and LARGE means Q<=abs(f(i)). Given a retained list R and prescribed start u, require u and u+sum(R.map(f)) to be in [0,C]. For EVERY literal occurrence R=R0++[i]++R1 with i LARGE, require BOTH u+sum(R0.map(f)) and u+sum(R0.map(f))+f(i) to be in [0,C]. These are the departure and arrival measured in the retained word itself. R may have illegal internal SMALL prefixes and incompatible opposite LARGE steps. No old legal ordering, deletion shift, source geometry, supplied favorable order, nonzero-weight hypothesis or distinctness hypothesis occurs in the theorem.

The output E.Perm(R) preserves every physical occurrence with its multiplicity. Its LARGE filter equals R's LARGE filter as a literal LIST, preserving the order of all retained LARGE occurrences. InStrip(f,C,u,E) includes both endpoints and every internal height. The existing inStrip_prefix gives every natural take, including zero and saturated overlength takes, at exactly u. Equal weights do not identify labels, and repeated labels are also permitted. When R is Nodup, the permutation gives E.Nodup.

There is one structural induction scanning the unprocessed suffix B while carrying the complete unfinished SMALL batch T. A SMALL head is appended to T without imposing a bound on its old prefix. At the next LARGE i, the stated departure is the endpoint of T and its arrival is the start for the remaining suffix. For positive p and negative n in T, integrality and the strict SMALL bounds give f(p)-f(n)<=2Q-2<=C. Invoke the existing SmallStepOrdering.exists_order_between on ALL T between its proved endpoints. Append the actual LARGE i, reset T to empty and continue from its arrival. At exhaustion the same ordering theorem handles the complete final batch. Permutation, filter_append and inStrip_append compose the witnesses. The scan has no bound on the number, signs or sizes of the SMALL batches or the number of retained LARGE occurrences.

Write the unique occurrence decomposition R=B0++[l1]++B1++...++[lr]++Br, with each Bj the complete intervening SMALL batch. The product of the symmetric groups on the positions of B0,...,Br acts by independent permutations within those batches. The construction stays in this orbit: it changes no batch's physical multiset and moves no occurrence across a retained LARGE. Batch start and end heights are invariant under this action. They are precisely the global start and endpoint and both sides of every LARGE. A strip representative necessarily puts all these invariant heights in [0,C]; the construction supplies the converse. The formal theorem exports sufficiency, exact physical Perm, literal LARGE-filter equality and InStrip. The product-permutation action identifies these boundary heights as the complete invariant obstruction.

For exact physical deletion, let A=U++B be an original-zero strip-legal Nodup word and let D be a set of its actual SMALL labels. Keep U literally before the earliest deletion, with U=A when D is empty, and filter exactly D out of B to obtain R. Let u=mass(U). The unchanged U is legal. For any ordering Dlist of the deleted physical labels, the filter partition gives (U++R++Dlist).Perm(A), hence u+mass(R)=mass(A)-mass(Dlist). If this endpoint and both retained LARGE boundaries lie in [0,C], apply the theorem to R and append the resulting E to U. This constructs Astar=U++E with every original-zero prefix legal, Astar.Nodup, (Astar++Dlist).Perm(A), and the complete original LARGE filter preserved.

At an original LARGE occurrence with departure H and signed deleted mass delta strictly before it, the retained departure and arrival are H-delta and H+f(i)-delta. Thus the exact old-height test is delta<=H<=C+delta and delta<=H+f(i)<=C+delta. The signed delta can vary from boundary to boundary; the generic theorem introduces no constant-shift or sign premise. This reconstructs a prefix when its actual boundary test holds. It supplies neither a proof that the test always holds at a global minimum nor a full Circle C3.1 exchange.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/LargeSkeletonOrdering.exists_order_preserving_large`
- Dependency: [D5/S3/Combinatorics/Circle/SmallStepOrdering](SmallStepOrdering.md)
