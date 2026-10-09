# Kasel's displacement ladder

## Abstract

Kasel's displacement ladder equals m minus two at every horizon four to the m, for m at least two.

**Definition 1.1 (The exact displacement-ladder claim).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.claim`

*Formalization.* `D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m at least two, there exist natural-valued stage and fibre-position functions s and r that form a valid normalized scheme on SA m, and s(v) is at most floor(block(v)/2) plus m minus two for every distinguished value v. Conversely, every valid normalized scheme on SA m has a distinguished value v with s(v) at least floor(block(v)/2) plus m minus two. Thus the minimum over schemes of the maximum distinguished displacement is L(m)=m-2 at horizon 4^m.

**Theorem 1.2 (Kasel's conjectured growth is proved).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.result` (`✓ std3`). ∎

*Resolves.* `Problems/kasel-2026-displacement-ladder` (proved) by `D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kasel-2026-displacement-ladder","declaration_gid":"D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The upper construction puts 3 and 4 at stage one and every other value at stage m, ordered within parity by target-biased binary reversal. It proves injectivity, normalization and avoidance of both monotone three-term arithmetic progressions. The lower bound converts the concatenation order into predecessor ranks and applies the frozen Erdos-Graham order-gadget obstruction at scale 2*4^(m-1); the case m=2 follows from normalization. Combining these bounds proves claim. This resolves the displacement-ladder conjecture in Appendix B.4, while the parent Erdos Problem 197 remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.result`
- Dependency: [D5/S3/Combinatorics/Permutation/KaselDisplacementLadderLower](KaselDisplacementLadderLower.md)
- Dependency: [D5/S3/Combinatorics/Permutation/KaselDisplacementLadderUpper](KaselDisplacementLadderUpper.md)
