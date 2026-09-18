# Shieh–Yang–Yu Conjecture 6.2 isolated probe

## Falsifiable predictions (registered before checks)

1. An independent Python implementation of West's stack map composed with reversal of each valley run reproduces Theorem 4.4 fixed-point counts for n = 1,...,8: 1,1,2,4,9,23,65,199, and Theorem 4.2 sortable counts 2^(n-1).
2. There is no cycle of length at least two among permutations of 1,...,n for 1 <= n <= 8.
3. At every non-fixed permutation in that range, the reversed output word is strictly larger in lexicographic order than the reversed input word.

These are predictions, not measured results. The source fidelity check precedes execution of the Python experiment. The preregistration defines the barred-pattern stack map by the proved right-hand side of Proposition 3.5; that boundary is retained explicitly.

## Status

Unverified: source fidelity, numerical predictions, library reuse, and Lean proof. No mathematical conclusion is claimed yet.
