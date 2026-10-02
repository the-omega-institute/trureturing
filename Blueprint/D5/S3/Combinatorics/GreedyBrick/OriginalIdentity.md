# The Greedy-Brick All-Index Identity

## Abstract

The first brick widths in every positive row satisfy the greedy-brick composition identity.

Bricks have widths 1,2,3,... and unit height. Each brick occupies the highest fully supported row as close to the vertical axis as possible. Rows are numbered from one. The deterministic capacity trajectory is conjugate to the literal row scan and has one common labelled rectangle history. Every positive row has a least birth. The width of its first brick equals that birth's brick index.

**Definition 1.1 (The literal first-birth sequence).**

$$\operatorname{a}\left(m\right) = \operatorname{if} 1 \le m \operatorname{then} \operatorname{birth}\left(m\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive m, birth(m) is the least brick index at which the actual trajectory has m rows. Its existence is proved for every m. The value at zero is unused.

**Theorem 1.2 (Udovenko's all-index identity).**

$$\forall m: \mathbb{N}, 1 \le m \implies \operatorname{a}\left(\operatorname{a}\left(m\right)\right) = \left\lfloor\frac{\operatorname{a}\left(m\right) \cdot \left(\operatorname{a}\left(m\right) + 3\right)}{2}\right\rfloor - m$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a395531-greedy-brick-all-index` (proved) by `D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a395531-greedy-brick-all-index","declaration_gid":"D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.result","resolution_kind":"proved"} -->

*Citation.* Aleksei Udovenko (2026). *OEIS A395531, greedy-brick row births*. URL: <https://oeis.org/A395531/internal>.

*Commentary.*

At a rest endpoint, the least zero capacity chooses the length of the next block. An induction through the positive capacity prefix shows that no row is born strictly before that block ends. The cofinal rest clock therefore identifies every literal least row birth with its event-birth endpoint.

Write b(m) for this common birth width. The successor band places a renewal before birth b(m) exactly when its immediate predecessor is before birth m. Successor and predecessor are inverse on these two cuts and preserve bin labels. Endpoint increments telescope to their weights. Births through b(m) contribute b(m)(b(m)+1)/2 and renewals contribute b(m)-m. Adding these weights gives the stated identity. This argument does not require the chronological renewal labels to copy an earlier word.

## References

- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.a`
- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/OriginalIdentity.result`
- Dependency: [D5/S3/Combinatorics/GreedyBrick/LiteralRestTrace](LiteralRestTrace.md)
