# Lacunary sequences and their counting bound

## Abstract

A sequence whose consecutive ratios stay above a constant greater than one dominates a geometric sequence, so only logarithmically many of its terms lie below a bound.

Lacunarity is a lower bound on consecutive ratios, so it propagates by induction into a lower bound by a geometric sequence. Inverting that bound logarithmically is what limits how many terms can stay small.

**Definition 1.1 (Lacunary sequences).**

Lean statement: `D5/S3/Arith/Lacunary/LacunarySequence.IsLacunary`

*Formalization.* `D5/S3/Arith/Lacunary/LacunarySequence.IsLacunary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsLacunary a c holds when c exceeds one, every term of a is positive, and c times a term is at most the next term.

**Theorem 1.2 (Geometric domination).**

Lean statement: `D5/S3/Arith/Lacunary/LacunarySequence.geometric_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lacunary/LacunarySequence.geometric_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lacunary with ratio c and every index n, the initial term times the n-th power of c is at most the n-th term. Induction on n: the base case is an equality, and the step multiplies the inductive inequality by the positive number c and then applies the lacunarity inequality at n.

**Theorem 1.3 (The counting bound).**

Lean statement: `D5/S3/Arith/Lacunary/LacunarySequence.card_lt_of_lacunary`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lacunary/LacunarySequence.card_lt_of_lacunary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a is lacunary with ratio c and each of its first N terms is at most x, then N is at most the larger of zero and the logarithm of x divided by the initial term, taken to base c, plus one. For a nonempty prefix the last of those terms gives the n-th power of c bounded by x divided by the initial term; positivity of the initial term permits the division, the logarithm to base c is increasing because c exceeds one, and the logarithm of a power of the base is the exponent. The empty prefix has no term to bound, so the conclusion there rests on the stated maximum being nonnegative. That maximum is necessary: for the sequence of powers of two with ratio two and bound one quarter, the hypothesis at N equal to zero holds vacuously while the logarithm plus one is negative.

## References

- Truth anchor: `D5/S3/Arith/Lacunary/LacunarySequence.IsLacunary`
- Truth anchor: `D5/S3/Arith/Lacunary/LacunarySequence.card_lt_of_lacunary`
- Truth anchor: `D5/S3/Arith/Lacunary/LacunarySequence.geometric_lower_bound`
