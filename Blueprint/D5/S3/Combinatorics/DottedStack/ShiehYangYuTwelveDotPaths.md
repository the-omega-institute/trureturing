# Signed Excursions and Balanced Bridges

## Abstract

Colored Dyck excursions correspond bijectively to balanced words of up and down steps.

**Theorem 1.1 (The first return of an upward bridge).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths.bridge_first_return`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths.bridge_first_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every balanced word of up and down steps beginning with an up step, there is a unique pair consisting of a Dyck path and a balanced suffix such that the word is that path enclosed between an up step and a down step, followed by the suffix. Balanced means that the numbers of up and down steps are equal; no nonnegativity condition is imposed on the suffix. The enclosed prefix ends at the first return to height zero.

**Definition 1.2 (Reflect colored excursions).**

Lean statement: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths.signed_bridge_equiv`

*Formalization.* `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths.signed_bridge_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

For every natural number m, signed_bridge_equiv is a bijection from finite lists of pairs consisting of a Boolean color and a Dyck path, with the sum of the path semilengths plus one for each pair equal to m, to words with exactly m up steps and m down steps. Each path is enclosed between an up step and a down step. A false color leaves this excursion unchanged; a true color exchanges all up and down steps. Concatenating these signed excursions gives the bridge. The inverse splits at successive returns to height zero, reflects excursions that begin with a down step, and removes the enclosing steps.

## References

- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths.bridge_first_return`
- Truth anchor: `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths.signed_bridge_equiv`
- Dependency: [D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck](ShiehYangYuTwelveDotDyck.md)
