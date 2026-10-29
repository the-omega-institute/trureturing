# The refined ceiling at every depth

## Abstract

The refined ceiling at every depth for the actual multiset game.

The mathematical targets are due to Satyam Tyagi. This module supplies their Lean proofs in the native Divisor Nim model, reusing the existing independently checked game-theoretic library.

For a positive Divisor Nim position P with minimum two-adic depth k and a distinguished heap H in P, the native Sprague--Grundy value is at most 2H - H/2^k + 1, which is at most 2H. No restriction on heap count, size or numerical minimality is used. The original minimum-heap proposition follows immediately.

**Theorem 1.1 (Every distinguished heap).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_reference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on minimum depth. Low-depth options fit the previous ceiling. For quotient H/2^k at least three, save the exceptional removal H-2^k: on H it leaves a minimum dyadic heap and fits the old budget; on another heap it cannot be legal. Quotient one uses the prior independent twice-minimum bound; quotient two uses the penultimate independent reference recurrence, with its established large-exponent inequality and exact small-exponent arithmetic.

**Theorem 1.2 (The requested minimum-heap statement).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_statement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_statement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete RevisedBoundStatement holds for every positive position, all natural H,k with HasDepth P k, H in P, and H numerically minimum. The theorem includes power-of-two minima; the independent old bound is reused without circularity.

**Theorem 1.3 (The full chain of inequalities).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual value is bounded by revisedCeiling H k and that ceiling is at most twice H. Divisibility by 2^k and positivity make the dyadic quotient at least one.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_chain`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_reference`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.revised_bound_statement`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimFixedBoard](DivisorNimFixedBoard.md)
