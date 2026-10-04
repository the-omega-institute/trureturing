# The Initial Parity Pattern

## Abstract

Finiteness of the alphabet forces an apwenian substitution fixed point to begin with one, an even letter and one.

**Theorem 1.1 (The forced initial pattern).**

Lean statement: `D5/S3/Combinatorics/Apwenian/GuoHanPrefix.initial_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apwenian/GuoHanPrefix.initial_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ying-Jun Guo, Guo-Niu Han (2025). *On a family of automatic apwenian sequences*. DOI: [10.1016/j.disc.2025.114399](https://doi.org/10.1016/j.disc.2025.114399). URL: <https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf>.

*Commentary.*

Let Sigma be a finite alphabet of nonnegative integers in which every odd letter equals one. Let p be an integer at least two, let sigma assign a word of length p to each nonnegative integer, and let a take values in Sigma and satisfy a(np + r) = sigma(a(n), r) for all nonnegative n and all r from zero through p minus one. If a is apwenian, then a(1) has image zero modulo two and a(2) = 1. Since a(0) = 1, the initial parity pattern is 101. The conclusion does not require every word assigned by sigma to every letter of Sigma to remain in Sigma.

## References

- Truth anchor: `D5/S3/Combinatorics/Apwenian/GuoHanPrefix.initial_prefix`
- Dependency: [D5/S3/Combinatorics/Apwenian/GuoHanDyadic](GuoHanDyadic.md)
