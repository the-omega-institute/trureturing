# Dyadic Expansion of the Apwenian Recursion

## Abstract

Iterating the apwenian recursion expresses each entry as the sum over a consecutive interval of binary descendants.

**Theorem 1.1 (Sum over binary descendants).**

Lean statement: `D5/S3/Combinatorics/Apwenian/GuoHanDyadic.dyadic_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apwenian/GuoHanDyadic.dyadic_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ying-Jun Guo, Guo-Niu Han (2025). *On a family of automatic apwenian sequences*. DOI: [10.1016/j.disc.2025.114399](https://doi.org/10.1016/j.disc.2025.114399). URL: <https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf>.

*Commentary.*

For every sequence b in the integers modulo two satisfying b(n) = b(2n + 1) + b(2n + 2) for all nonnegative n, and every pair of nonnegative integers h and n, b(n) is the sum of b(2^h(n + 1) - 1 + j) over j from zero through 2^h minus one. The sum is taken modulo two. At depth zero it consists of b(n) alone; at each successive depth the two descendants of each term partition the next consecutive interval.

## References

- Truth anchor: `D5/S3/Combinatorics/Apwenian/GuoHanDyadic.dyadic_expansion`
- Dependency: [D5/S3/Combinatorics/Apwenian/GuoHanBlocks](GuoHanBlocks.md)
