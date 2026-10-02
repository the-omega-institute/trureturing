# A Component-Weighted Indecomposable Recurrence

## Abstract

Component lists determine the active-position polynomial of indecomposable Fishburn permutations avoiding 2431 and 3241.

**Theorem 1.1 (The active-position polynomial recurrence).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable.inductive_counting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable.inductive_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Fix a positive integer n and call a position in a Fishburn permutation avoiding 2431 and 3241 active when insertion of its new maximum preserves those conditions. Let the component lists be all lists of nonempty sum-indecomposable permutations whose direct sum is a Fishburn permutation of length n avoiding both patterns. For a component list with r components, let t be the number of components after the first and let a be the number of active positions in its first component. The sum over sum-indecomposable avoiders of length n + 1 of X to the power their number of active positions minus two equals the sum over component lists of X to the power r minus one, plus the sum over component lists of X to the power one when t is zero or to the power t otherwise, multiplied by the sum of X to the power e over nonnegative e strictly less than a minus two. This is an identity of polynomials with rational coefficients, and subtractions in exponents and range lengths are truncated at zero.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable.inductive_counting`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSumInsertion](FishburnBasicSumInsertion.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBSums](FishburnTenThirteenBSums.md)
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBUpdates](FishburnTenThirteenBUpdates.md)
