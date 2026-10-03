# Ordered low-subword recovery

## Abstract

Increasing slot order transports low-subword deletion and reads a replacement permutation exactly.

**Theorem 1.1 (Deletion and replacement in increasing low-slot order).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledOrderedRecovery.shared_ordered_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/CoupledOrderedRecovery.shared_ordered_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Consider families cut, slotOrder, lowWord and replace on finite permutations. At every size n and threshold T at most n, slotOrder is an order isomorphism from Fin(T) onto the positions u whose label sigma(u) is less than T. Assume cut deletes one position and its label using the two increasing finSuccAbove equivalences; lowWord reads sigma along slotOrder and identifies the low labels with Fin(T) using Fin.castLEOrderIso; and replace composes sigma with the low-label subtype permutation that sends lowWord sigma to the requested permutation rho. These assumptions are equalities of the actual operations at every size, not assumed inverse laws.

Both conclusions hold. First, for every n and L with L at most n, every sigma on Fin(n plus one), every position t and every hypothesis sigma(t) less than L plus one, let so be slotOrder sigma at threshold L plus one and r be so.inverse(t). Then lowWord(cut sigma t) at threshold L equals cut(lowWord sigma at threshold L plus one) at r. Second, for every n and T with T at most n, every permutation S on Fin(n), and every rho on Fin(T), reading lowWord after replace S rho returns rho, and replacing once more by the original lowWord S returns S.

Deleting t carries each surviving low slot through t.succAbove. This gives an order isomorphism onto the original low slots with t removed. Uniqueness of order isomorphisms between these finite chains identifies their enumerations. The row-label deletion follows the same increasing standardization. A low-label replacement preserves the set of low slots, so the same increasing enumeration reads the requested labels; applying the inverse low-label change restores the original permutation.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledOrderedRecovery.shared_ordered_recovery`
