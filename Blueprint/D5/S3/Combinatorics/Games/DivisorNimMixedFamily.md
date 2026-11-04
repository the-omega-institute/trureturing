# The complete mixed two/four formula

## Abstract

The complete mixed two/four formula for the actual multiset game.

The mathematical targets are due to Satyam Tyagi. This module supplies their Lean proofs in the native Divisor Nim model, reusing the existing independently checked game-theoretic library.

Write A for r copies of two and s copies of four, where r,s are positive, and omit a varying heap of size zero. The actual SG sequence is one at n congruent to one modulo four, two at n congruent to three modulo four, and three times the parity of r+floor(n/2) at even n. Multiplicities and n are unbounded.

**Theorem 1.1 (The complete native mixed formula).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimMixedFamily.mixed_formula_statement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimMixedFamily.mixed_formula_statement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the established native recurrence and outcome theorem. Winning even boards have options of values zero, one and two. Odd phases follow by strong induction. A second induction on the number of fours excludes value three from all followers of winning even boards. Deleting the last two is included: the remaining pure-four board has a legal four-to-two option with value three by the smaller-family theorem, or the explicitly proved one-two boundary. The omitted-zero singleton-four case is handled directly. No finite table substitutes for the infinite-family proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimMixedFamily.mixed_formula_statement`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimGcdTwo](DivisorNimGcdTwo.md)
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimRevisedTargets](DivisorNimRevisedTargets.md)
