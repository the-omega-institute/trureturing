# Substitution Blocks and Parity Identification

## Abstract

Equal letters determine equal iterated substitution blocks, and the apwenian recursion identifies parity once every even position is one.

**Theorem 1.1 (Equal letters have equal iterated blocks).**

Lean statement: `D5/S3/Combinatorics/Apwenian/GuoHanBlocks.equal_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apwenian/GuoHanBlocks.equal_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ying-Jun Guo, Guo-Niu Han (2025). *On a family of automatic apwenian sequences*. DOI: [10.1016/j.disc.2025.114399](https://doi.org/10.1016/j.disc.2025.114399). URL: <https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf>.

*Commentary.*

Let p be a positive integer, let sigma assign a word of length p of nonnegative integers to each nonnegative integer, and let a satisfy a(np + r) = sigma(a(n), r) for every nonnegative n and every r from zero through p minus one. If a(n) = a(m), then for every nonnegative integer t and every j from zero through p^t minus one, a(n p^t + j) = a(m p^t + j). The equality is between actual letters, without passing to parity.

**Theorem 1.2 (Even positions determine period doubling).**

Lean statement: `D5/S3/Combinatorics/Apwenian/GuoHanBlocks.identify_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apwenian/GuoHanBlocks.identify_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ying-Jun Guo, Guo-Niu Han (2025). *On a family of automatic apwenian sequences*. DOI: [10.1016/j.disc.2025.114399](https://doi.org/10.1016/j.disc.2025.114399). URL: <https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf>.

*Commentary.*

Let b be a sequence in the integers modulo two satisfying b(n) = b(2n + 1) + b(2n + 2) for every nonnegative integer n. If b(2n) = 1 for every nonnegative n, then b(n) equals the image of P(n) modulo two for every nonnegative n, where P is the period-doubling sequence. The recursion gives b(2n + 1) = 1 - b(n), so induction determines every entry.

## References

- Truth anchor: `D5/S3/Combinatorics/Apwenian/GuoHanBlocks.equal_blocks`
- Truth anchor: `D5/S3/Combinatorics/Apwenian/GuoHanBlocks.identify_parity`
- Dependency: [D5/S3/Combinatorics/Apwenian/GuoHanDefs](GuoHanDefs.md)
