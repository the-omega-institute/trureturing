# The repaired integer weight

## Abstract

The actual repaired deletion increases the integer inversion-minus-forbidden-count weight by the sum of its two digits.

All positions and labels are zero-based. A row permutation sigma on Fin(k plus two) and a column permutation pi on Fin(k plus one) determine the front label sigma(pi(i)) and the back label sigma(pi(i) plus one). The increment occurs in the position before evaluating sigma. The distinguished back target is sigma(0).

**Definition 1.1 (The row or column inversion count).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.I`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.I` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For a permutation S of Fin(n), form the list of its natural label values in increasing position order. I(S) is ListInversions.inv of this List.ofFn word, counting pairs of positions u less than v with S(v) less than S(u).

**Definition 1.2 (Inversions minus both forbidden counts).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.E`

*Formalization.* `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For thresholds F and G on Fin(K), a row permutation S on Fin(K plus one), and a column permutation p on Fin(K), E(F,G,S,p) is I(S) plus I(p) minus the first coordinate of the actual ForbiddenCount F G S p minus its second coordinate. Each of the four natural counts is cast to the integers before subtraction. The back count includes its distinguished endpoint.

**Theorem 1.3 (The complete repaired digit increment).**

Lean statement: `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.actual_repaired_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.actual_repaired_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For arbitrary natural numbers k, L and B with L at most B and B at most k plus one, let F and G map Fin(k plus one) to natural numbers. Let sigma permute Fin(k plus two) and pi permute Fin(k plus one). Assume F and G are monotone, F(i) is at most G(i) for every i, F(0) equals L plus one, G(0) equals B plus one, and the pair is Eligible F G sigma pi. Let z be the literal output of actualAlgorithms.phi on this pair. Put Ft(i) equal to F(i.succ) minus one and Gt(i) equal to G(i.succ) minus one for i in Fin(k), using natural subtraction. Then E(F,G,sigma,pi) equals E(Ft,Gt,z.row,z.column) plus the integer casts of z.d and z.b. Here z.row is z.1.1, z.column is z.1.2, z.d is z.2.1 and z.b is z.2.2.

To compute the actual output, set t to pi(0), s to cut sigma t.castSucc, and p to cut pi 0. Read theta as lowWord sigma at threshold L plus one, and let q be the position of its maximum label L. Delete that maximum to obtain rho, replace the labels below L in s by rho in their increasing slot order, and call the resulting row permutation sdag. The two digits are d equals L minus q.val and b equals the number of positions u less than t with s(u) less than B.

For words with the same low slots and identical high entries, the full inversion difference equals the inversion difference of their ordered low subwords. This identity holds for arbitrarily interleaved low slots. Single-entry deletion then gives I(sigma) equals I(sdag) plus H_A plus d, where H_A counts the original prefix labels at least L plus one. The column deletion contributes t. Partitioning that prefix at B plus one gives t equals H_G plus b. Ordinary forbidden-count contraction subtracts H_A and H_G; replacing low labels leaves the tail forbidden counts invariant.

The theorem includes k equal to zero, which has one original column and an empty column tail; L equal to zero; t equal to zero; and t equal to the final column position. An original zero-column pair has weight zero separately. The equality concerns this single repaired deletion.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.E`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.I`
- Truth anchor: `D5/S3/Combinatorics/Permutation/CoupledRepairedWeight.actual_repaired_weight`
- Dependency: [D5/S1/Digit/Carry/ListInversions](../../../S1/Digit/Carry/ListInversions.md)
- Dependency: [D5/S3/Combinatorics/Permutation/CoupledOrderedRecovery](CoupledOrderedRecovery.md)
- Dependency: [D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction](OrdinaryForbiddenCountContraction.md)
