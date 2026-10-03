# A bijection to second-position minima

## Abstract

For n at least four, T(n) bijects augmented(n-1) with the simple permutations of size n in C having their minimum second. The map undoT(n) is its inverse on both sets.

**Definition 1.1 (The recursive second-position construction).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.T`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The map T(n,p) is empty at n = 0. At positive n, if p is simple and its minimum is not second, increase its entries and insert one second. If p is simple with minimum second, let r = undoT(n-1,p): when r is simple, first inflate its first entry by 21, and otherwise use B(n-1), then increase the entries and insert one second. For non-simple p, increase the entries of B(n-1) and insert one second.

**Definition 1.2 (The reverse second-position construction).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.undoT`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.undoT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

The map undoT(n,p) is empty at n = 0. Otherwise delete the second entry and subtract one from the remaining values to obtain q. If q is simple, return q. If q = B(n-1), return E(floor((n-1)/2)) when n is even and T(n-1,E(floor((n-2)/2))) when n is odd. In the remaining case return T(n-1,deflateFirst(q)).

**Theorem 1.3 (A bijection to second-position minima).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.minimum_two_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.minimum_two_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For n at least four, T(n) bijects augmented(n-1) with the simple permutations of size n in C having their minimum second. The map undoT(n) is its inverse on both sets.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.T`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.minimum_two_bijection`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.undoT`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackDecreasing](PopStackDecreasing.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackM3Disjoint](PopStackM3Disjoint.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackVerticalContinuation](PopStackVerticalContinuation.md)
