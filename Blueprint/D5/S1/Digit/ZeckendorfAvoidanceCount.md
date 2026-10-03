# Conditional weighted avoidance count

## Abstract

Conditional weighted avoidance count.

**Definition 1.1 (Legal words with an entering bit).**

Lean statement: `D5/S1/Digit/ZeckendorfAvoidanceCount.legalWords`

*Formalization.* `D5/S1/Digit/ZeckendorfAvoidanceCount.legalWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

legalWords 0 b = [[]]. For n + 1, legalWords (n + 1) b lists the words 0 :: w for w in legalWords n 0, followed, when b = 0, by 1 :: w for w in legalWords n 1. It enumerates words of the specified length for which b :: w has no adjacent ones.

**Definition 1.2 (Final bit with empty-word convention).**

Lean statement: `D5/S1/Digit/ZeckendorfAvoidanceCount.endBit`

*Formalization.* `D5/S1/Digit/ZeckendorfAvoidanceCount.endBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

endBit b [] = b and endBit b (a :: w) = endBit a w. The entering bit is retained for an empty word; otherwise this is the last input bit.

**Definition 1.3 (Perron endpoint weight).**

Lean statement: `D5/S1/Digit/ZeckendorfAvoidanceCount.endpointWeight`

*Formalization.* `D5/S1/Digit/ZeckendorfAvoidanceCount.endpointWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b : Fin 2, endpointWeight b is Real.goldenRatio if b = 0 and 1 otherwise. The endpoint weight retains the last bit when successive legal blocks are counted.

**Definition 1.4 (Aligned block avoidance with a short suffix).**

Lean statement: `D5/S1/Digit/ZeckendorfAvoidanceCount.blockWords`

*Formalization.* `D5/S1/Digit/ZeckendorfAvoidanceCount.blockWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

blockWords r 0 b = legalWords r b. For k + 1, blockWords r (k + 1) b concatenates each p in legalWords 14 b with p ≠ B1 to every word in blockWords r k (endBit b p). These length-14k+r words avoid B1 at the aligned block positions; words avoiding B1 everywhere form a subset.

**Theorem 1.5 (Conditional weighted avoidance count).**

Lean statement: `D5/S1/Digit/ZeckendorfAvoidanceCount.uniform_avoidance_count`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfAvoidanceCount.uniform_avoidance_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem uniform_avoidance_count (H : ℕ) : ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length ≤ Real.goldenRatio ^ (H + 1) * (1 - (Real.goldenRatio ^ (14 : ℕ))⁻¹) ^ (H / 14)`.

Legal words avoiding 00010101001000 have count at most φ^(H+1)(1−φ^(−14))^floor(H/14). Endpoint weights φ and 1 retain the entering bit across each 14-block. Removing the allowed block under either entering state gives the uniform conditional transfer loss; the final short suffix is counted explicitly.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfAvoidanceCount.blockWords`
- Truth anchor: `D5/S1/Digit/ZeckendorfAvoidanceCount.endBit`
- Truth anchor: `D5/S1/Digit/ZeckendorfAvoidanceCount.endpointWeight`
- Truth anchor: `D5/S1/Digit/ZeckendorfAvoidanceCount.legalWords`
- Truth anchor: `D5/S1/Digit/ZeckendorfAvoidanceCount.uniform_avoidance_count`
- Dependency: [D5/S1/Digit/ZeckendorfContextualReplacement](ZeckendorfContextualReplacement.md)
