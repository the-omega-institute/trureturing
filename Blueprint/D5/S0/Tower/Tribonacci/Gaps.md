# Tribonacci Gaps

## Abstract

Sorted Tribonacci name values have exactly three adjacent lengths from level three.

A joint strong induction tracks both internal adjacent differences and the terminal distance to one. The three prefix blocks scale lower-level gaps by t^-1, t^-2, and t^-3, while both block boundaries scale terminal gaps.

**Theorem 1.1 (Consecutive Tribonacci three-gap invariant).**

Lean statement: `D5/S0/Tower/Tribonacci/Gaps.consecutive_nameValue_gap`

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Gaps.consecutive_nameValue_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every consecutive difference is t^-Q, t^-(Q+1), or the sum of t^-(Q+1) and t^-(Q+2).

**Theorem 1.2 (Indexed Tribonacci values increase strictly).**

$$\forall Q \in N,\; \operatorname{StrictMono}\left(\operatorname{indexedNameValue}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Gaps.indexed_nameValue_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All three possible differences are positive, so positivity of adjacent steps promotes to strict monotonicity on the complete finite interval.

**Theorem 1.3 (Tribonacci name values are injective).**

$$\forall Q \in N,\; \operatorname{Injective}\left(\operatorname{tribonacciNameValue}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Gaps.tribonacciNameValue_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strictness of the indexed values and bijectivity of the prefix enumeration separate every pair of admissible names.

**Theorem 1.4 (Exact Tribonacci three-gap spectrum).**

Lean statement: `D5/S0/Tower/Tribonacci/Gaps.adjacent_gap_spectrum`

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/Gaps.adjacent_gap_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The level-three witnesses persist in the zero-prefix block at every higher level, so all three candidate lengths occur. Their strict ordering also proves that the spectrum has cardinality three.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/Gaps.adjacent_gap_spectrum`
- Truth anchor: `D5/S0/Tower/Tribonacci/Gaps.consecutive_nameValue_gap`
- Truth anchor: `D5/S0/Tower/Tribonacci/Gaps.indexed_nameValue_strictMono`
- Truth anchor: `D5/S0/Tower/Tribonacci/Gaps.tribonacciNameValue_injective`
- Dependency: [D5/S0/Tower/Tribonacci/Values](Values.md)
