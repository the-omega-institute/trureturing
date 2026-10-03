# 231-Avoiding Permutations and Dyck Paths

## Abstract

A bijection from 231-avoiding permutations to Dyck paths carries left-to-right maxima to primitive excursions.

**Definition 1.1 (Encode an avoiding permutation).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_encode`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_encode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every natural number m, avoiding_encode maps a 231-avoiding permutation of [1,...,m] to a Dyck path of semilength m. A Dyck path has up and down steps, starts and ends at height zero, and never has negative height. The empty permutation maps to the empty path. A nonempty permutation splits at its maximum into a left permutation of [1,...,k] and a right permutation whose values are decreased by k. Its path is the left path followed by the right path enclosed between an up step and a down step.

**Definition 1.2 (The last primitive excursion).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.lastExcursion`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.lastExcursion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

The map lastExcursion returns a pair of Dyck paths. On the empty path it returns two empty paths. On a nonempty path, the first component is the prefix preceding the last primitive excursion and the second is the path inside that excursion, with its initial up step and final down step removed. A primitive excursion is a nonempty Dyck path that returns to height zero only at its end.

**Theorem 1.3 (Reconstruct the last excursion).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.last_excursion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.last_excursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

Every nonempty Dyck path is the concatenation of the first component of lastExcursion and the second component enclosed between an up step and a down step. Conversely, for any Dyck paths A and B, lastExcursion applied to A followed by B enclosed between an up step and a down step returns exactly the pair (A,B).

**Definition 1.4 (Decode a Dyck path).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_decode`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_decode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every Dyck path of semilength m, avoiding_decode returns a 231-avoiding permutation of [1,...,m]. The empty path gives the empty permutation. For a nonempty path, write (A,B) for lastExcursion and let k be the semilength of A. The decoded word is the decoded word of A, followed by the maximum m, followed by the decoded word of B with k added to every entry.

**Definition 1.5 (Interiors of primitive excursions).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.excursions`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.excursions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every Dyck path, excursions is the ordered list of the interiors of its primitive excursions. Each interior is obtained by removing the initial up step and final down step of its excursion. The empty path gives the empty list. A nonempty path contributes its first excursion's interior, followed by the list obtained from the remaining path.

**Theorem 1.6 (Inverse maps and record counts).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every natural number m and every 231-avoiding permutation of [1,...,m], decoding its encoded path recovers the permutation. For every Dyck path, encoding its decoded permutation recovers the path. For every such permutation, the number of record values equals the length of the excursions list of its encoded path, so records correspond in number to primitive excursions.

**Definition 1.7 (Dyck paths as lists of excursion interiors).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.excursion_equiv`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.excursion_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

The bijection excursion_equiv sends a Dyck path to its excursions list and sends any finite list of Dyck paths back to the concatenation obtained by enclosing each member between an up step and a down step. These two maps are inverse on all Dyck paths and all finite lists of Dyck paths, including the empty path and empty list.

## References

- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_decode`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_encode`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.avoiding_inverse`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.excursion_equiv`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.excursions`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.lastExcursion`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.last_excursion`
- Dependency: [D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre](ShiehYangYuTwelveDotFibre.md)
