# Two Adaptive Circular Deletion Readouts

## Abstract

On every fixed finite support of at least three labels, two labeled deletions from the same original oriented circle fail to reconstruct it, even when the second label is chosen deterministically from the first residual.

Let alpha be any type with decidable equality, and let A be a finite set of labels. Cycle(alpha) identifies lists under rotation and retains orientation. SupportedCircle(A) is the subtype of cycles C with C.Nodup and C.toFinset = A. Thus every label of A occurs exactly once. Labels(A) denotes the subtype of labels belonging to A; Function(U,V) denotes functions from U to V.

Fix a first label x in Labels(A). A deterministic policy sigma maps every Cycle(alpha) to Labels(A). For an original C, put B = delete(x,C) and z = sigma(B). The definition adaptiveTrace(A,x,sigma)(C) retains the ordered tuple (x,B,z,delete(z,C)). Both deletions are readouts of the same original C. The second label may equal x, and all residual labels retain their original names. A fixed x and sigma already supply every policy for this two-query model, since A and the first label are fixed.

**Theorem 1.1 (Two Adaptive Readouts Are Noninjective).**

$$\forall alpha \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(alpha\right)] \forall A \in \mathrm{Finset}\left(alpha\right),\; (3 \le \mathrm{card}\left(A\right)) \Rightarrow (\forall x \in \mathrm{Labels}\left(A\right),\; \forall sigma \in \mathrm{Function}\left(\mathrm{Cycle}\left(alpha\right), \mathrm{Labels}\left(A\right)\right),\; \neg \mathrm{Injective}\left(\mathrm{adaptiveTrace}\left(A, x, sigma\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/AdaptiveTwoReadout.no_adaptive_two_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every A of cardinality at least three, every first label x in A, and every deterministic policy sigma from Cycle(alpha) to Labels(A), the full map adaptiveTrace(A,x,sigma) on SupportedCircle(A) is not injective. There are distinct supported original circles with the same first label, first residual, second label, and second residual. This includes every support of cardinality at least four.

The proof works on every supported first-residual branch B, rather than choosing a label pair before B is known. Write z = sigma(B). If z differs from x, rotate a representative of B to z::R. Then C is the cycle of x::z::R and D is the cycle of x::(R++[z]). Both are nodup with exact support A. Deleting x gives z::R and R++[z], which represent the same oriented cycle B. Deleting z gives x::R in both cases. The bound on A makes R nonempty. If C equaled D, CyclicInsertionGap.anchored_coe_injective at x would give z::R = R++[z]; their first entries would force z to occur in R, contrary to nodup. This is the construction in adjacent_pair_collision.

If z equals x, choose any label of A.erase(x) and use the same two adjacent insertions. The lemma two_gap_collision retains their distinctness and common first residual. Repeating x then returns B again on both original circles. The lemma adaptive_branch_collision combines these cases for an arbitrary B. Finally, exists_supported_residual supplies B from the toList of A.erase(x). Equality of the two full tuples contradicts injectivity on SupportedCircle(A).

The support restriction on the policy is essential: deleting an ambient label outside A would leave the original circle unchanged and reveal it. The model keeps the second deletion on the original circle, rather than deleting from the first residual. The proof does not use the paired-deletion fiber classification. The positive direction for supports of cardinality at most two remains a separate, unformalized boundary. This theorem gives a two-observation obstruction, not a general optimum or a mean-cost bound.

The result is repository-derived from the explicit insertion construction and the existing circular deletion API. The verified publisher abstracts of Permutation Reconstruction (DOI 10.37236/1149) and Permutation Reconstruction from Minors (DOI 10.37236/1092) describe deletion minors with order-preserving renumbering. The verified abstract of Reconstructing Permutations from Cycle Minors (DOI 10.37236/108) describes deletion in a permutation's disjoint-cycle decomposition, again reducing larger labels. Those abstract-level comparisons do not establish a prior theorem or priority for the exact fixed-label adaptive statement here. No literature novelty claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/AdaptiveTwoReadout.no_adaptive_two_reconstruction`
- Dependency: [D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction](DeletionReadoutReconstruction.md)
