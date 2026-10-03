# The five cases for a third-position minimum

## Abstract

Let p be a permutation of size at least five with minimum third, and form q by deleting that minimum and subtracting one from every remaining value. The permutation p is simple and in C if and only if q is a permutation in C reconstructing p by minimum insertion, and at least one of five cases holds: q is simple with minimum at zero-based position at least three; q is the second-entry inflation by 21 of a unique simple skeleton in C of size at least four whose minimum is not second; p is obtained by prepending two to a unique simple parent in C with minimum second while increasing its values other than one; p is obtained in the same way after second-entry inflation by 12 of a unique simple skeleton in C of size at least four with minimum second; or q belongs to D, ends in its minimum, and equals R at its size.

**Theorem 1.1 (The five cases for a third-position minimum).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackThirdDecomposition.minimum_three_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackThirdDecomposition.minimum_three_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a permutation of size at least five with minimum third, and form q by deleting that minimum and subtracting one from every remaining value. The permutation p is simple and in C if and only if q is a permutation in C reconstructing p by minimum insertion, and at least one of five cases holds: q is simple with minimum at zero-based position at least three; q is the second-entry inflation by 21 of a unique simple skeleton in C of size at least four whose minimum is not second; p is obtained by prepending two to a unique simple parent in C with minimum second while increasing its values other than one; p is obtained in the same way after second-entry inflation by 12 of a unique simple skeleton in C of size at least four with minimum second; or q belongs to D, ends in its minimum, and equals R at its size.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackThirdDecomposition.minimum_three_decomposition`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackCrossing](PopStackCrossing.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackLeftDecomposition](PopStackLeftDecomposition.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackMinimum](PopStackMinimum.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackPrime](PopStackPrime.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals](PopStackTerminalIntervals.md)
