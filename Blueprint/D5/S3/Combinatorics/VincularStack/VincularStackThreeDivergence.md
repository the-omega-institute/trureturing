# Different Push Decisions Force 231

## Abstract

A push permitted by the stack avoiding 3-12 but forbidden by the stack avoiding 312 forces a 231 occurrence.

**Theorem 1.1 (The structure of different push decisions).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDivergence.divergence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackThreeDivergence.divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Suppose an entry followed by a stack has distinct entries, the stack avoids classical 312, and pushing the entry creates classical 312 but not 3-12 with the entries playing 1 and 2 adjacent. Then the stack is a nonempty prefix followed by a high entry and a tail containing a low entry. Every entry of the prefix is less than the low entry, which is less than the inserted entry, which is less than the high entry. Insertion avoiding 312 pops exactly that prefix and leaves the inserted entry followed by the high entry and the tail; insertion avoiding 3-12 pops nothing and leaves the inserted entry followed by the original stack. Both resulting stacks contain classical 231.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackThreeDivergence.divergence`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic](VincularStackThreeBasic.md)
