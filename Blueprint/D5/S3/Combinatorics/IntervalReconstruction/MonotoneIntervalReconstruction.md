# Reconstruction from full interval sums

## Abstract

Unlabelled interval sums determine every nonnegative nondecreasing real list of length at least three.

**Theorem 1.1 (Zeros, equal entries and coincident observations).**

$$\forall A: \operatorname{List}\left(Real\right), \forall B: \operatorname{List}\left(Real\right), 3 \le \operatorname{length}\left(A\right) \Rightarrow \left(\operatorname{Nonnegative}\left(A\right) \Rightarrow \left(\operatorname{Nonnegative}\left(B\right) \Rightarrow \left(\operatorname{Nondecreasing}\left(A\right) \Rightarrow \left(\operatorname{Nondecreasing}\left(B\right) \Rightarrow \left(\operatorname{C}\left(A\right) = \operatorname{C}\left(B\right) \Rightarrow A = B\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IntervalReconstruction/MonotoneIntervalReconstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Norbert Hegyvári, Péter Pál Pach, Quanyu Tang (2026). *Consecutive sums and Reconstructing Problems*. URL: <https://arxiv.org/abs/2611.30462v1>.

*Commentary.*

A and B are arbitrary finite lists of exact real numbers. Nonnegative(L) means that every entry x of L satisfies 0≤x. Nondecreasing(L) means L.Pairwise (·≤·) in the original index order. Equal adjacent entries and zeros are allowed. C(L) is the multiset containing one occurrence of the inclusive sum from i through j for every 0≤i<j<length(L). All multiplicities are retained. The input provides neither interval labels nor singleton sums. Only length(A)≥3 is assumed; B has no supplied length bound, and the two lengths are not assumed equal.

The mathematical source is Omega.MonotoneIntervalReconstruction.list_reconstruct in OmegaMath.Combinatorics.MonotoneIntervalReconstruction. The D5 result is its book citation. The source defines intervals n as the filtered Cartesian product of range n with itself and maps each endpoint pair to the sum over Finset.Icc. Thus each interval contributes once, even when many pairs have the same value. The list accessor getD is used only at indices inside the list; its default does not affect C.

A contributes its whole-list interval, so C(A) is nonempty. Equality of observations gives an actual interval in B, forcing its length to be positive. Cardinality of C then determines the length: increasing a positive n strictly enlarges the interval set. Thus B also has length at least three. The maximum observation is the whole-list sum T. After removing exactly the single occurrence indexed by the whole list, the maximum is the sum S from index 1 to n−1. Every other proper interval omits either the first or the last entry; nonnegativity and nondecreasing order bound its sum by S. Hence the first entry is T−S. This argument also applies when T=S and the largest observed value has several occurrences.

For a known prefix of k entries, partition the actual endpoint pairs into j<k and j≥k. Their mapped multisets add to the full data. Equal prefixes give exactly equal first parts, which cancel with multiplicity. In the remaining multiset the boundary interval (k−1,k) occurs, and every remaining interval has value at least a(k−1)+a(k): its last two entries dominate that pair and all further entries are nonnegative. This is a statement about the minimum value; no unique occurrence is asserted. Equal residual data and the equal previous entry force equal next entries. Starting at k=1 recovers the second entry as well, and induction synchronizes the whole list.

Hegyvári, Pach and Tang, Consecutive sums and Reconstructing Problems, arXiv:2611.30462v1, Section 4.1, Proposition 4.1, supply the extremal initialization and residual-minimum proof route for positive strictly increasing integer lists. The real, zero and weak-order extension here is derived in this repository. The source and scope are recorded in Library/FiniteGeometry/hegyvari2026consecutivesums.md. This theorem claims mathematical uniqueness only; it makes no arithmetic-operation, bit-complexity or RAM bound and does not solve general Turnpike. The bounded source and Lean search does not establish worldwide novelty.

## References

- Truth anchor: `D5/S3/Combinatorics/IntervalReconstruction/MonotoneIntervalReconstruction.result`
