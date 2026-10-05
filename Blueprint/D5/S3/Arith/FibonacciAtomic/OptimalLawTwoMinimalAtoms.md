# Two Minimum Atoms in Every Optimal Law

## Abstract

Every positive attaining law has at least two labels at its minimum mass.

**Theorem 1.1 (At least two labels attain the minimum).**

$$(\forall m: \mathbb{N}, (\forall p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, ((2 \le m \land (\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{p}\left(i\right) = 1 \land \operatorname{cost}\left(p\right) = \operatorname{alpha}\left(m\right) \cdot \operatorname{inf}\left(\operatorname{range}\left(p\right)\right)) \to (\exists i: \operatorname{Fin}\left(m\right), (\exists j: \operatorname{Fin}\left(m\right), (i \neq j \land \operatorname{p}\left(i\right) = \operatorname{inf}\left(\operatorname{range}\left(p\right)\right) \land \operatorname{p}\left(j\right) = \operatorname{inf}\left(\operatorname{range}\left(p\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawTwoMinimalAtoms.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a strictly positive normalized real law on at least two labels. Its dyadic cost equals alpha(m) times the infimum of its finite range. The conclusion supplies two distinct labels i and j whose masses both equal that infimum.

Assume a unique minimum label k. The termination theorem places every larger atom on a dyadic grid. A common denominator gives positive integer numerators summing to a power of two; the least common denominator has positive depth, and the odd numerators form a nonempty even-cardinality set.

If the minimum numerator is odd, any other odd numerator is at least two larger, so moving one deepest dyadic leaf from that atom to the minimum raises the minimum mass while preserving the dyadic grid. If the minimum numerator is even and an odd numerator is at least three larger, the same one-leaf transfer applies.

In the remaining case there are two odd atoms with numerator exactly one above the even minimum. Moving one leaf from each to the minimum keeps the minimum mass fixed. All shallower floor counts weakly increase, with a strict increase at the preceding depth, while every deeper remainder is already zero. The resulting positive normalized law therefore has strictly smaller cost but the same optimal lower bound, a contradiction.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawTwoMinimalAtoms.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawNearestStrictCeiling](OptimalLawNearestStrictCeiling.md)
