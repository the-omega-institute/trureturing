# Classification when all intervals are prefixes

## Abstract

For n at least two, A(n) does not end in its minimum and B(n) does. A permutation of size n belongs to D and has every proper nontrivial interval starting at its first position if and only if it equals A(n) or B(n).

**Definition 1.1 (The nonterminal prefix family).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackFamilies.A`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackFamilies.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For even n, A(n) equals P(n/2). For odd n, A(n) is obtained by inflating the first entry of P(floor(n/2)) by 21.

**Definition 1.2 (The terminal prefix family).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackFamilies.B`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackFamilies.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Set B(2) = 21. At every other size n, B(n) is obtained by adding one to every entry of A(n-1) and appending one. Subtraction of nonnegative integers is truncated at zero.

**Theorem 1.3 (Classification when all intervals are prefixes).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackFamilies.prefix_families`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackFamilies.prefix_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

For n at least two, A(n) does not end in its minimum and B(n) does. A permutation of size n belongs to D and has every proper nontrivial interval starting at its first position if and only if it equals A(n) or B(n).

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackFamilies.A`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackFamilies.B`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackFamilies.prefix_families`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackPrefixShape](PopStackPrefixShape.md)
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackPrime](PopStackPrime.md)
