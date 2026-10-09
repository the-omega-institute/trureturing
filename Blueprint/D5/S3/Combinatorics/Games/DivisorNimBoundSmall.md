# Distinguished Heaps Two and Four

## Abstract

Paired dyadic remainders sharpen the bounds for small distinguished heaps.

**Theorem 1.1 (Discard bounded exceptional removals).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.refined_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.refined_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Low-depth removals are bounded by B. Any higher-depth removal with nonzero value must change a unique minimum-depth heap. If its value exceeds B, counting its possible amounts in A bounds the current value by B plus the cardinality of A plus one.

**Theorem 1.2 (A paired minimum-depth remainder).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.paired_remainder_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.paired_remainder_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the other heaps have minimum-depth count one at depth k and a legal removal leaves a positive heap at depth k, the follower has count two and value zero.

**Theorem 1.3 (The two largest dyadic divisors).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.power_divisor_high`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.power_divisor_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A divisor of two to the power k plus one whose valuation is at least k equals either two to the power k or two to the power k plus one.

**Theorem 1.4 (One exceptional removal remains).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.paired_pivot_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.paired_pivot_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When a pivot at depth k lies beside a unique heap at depth k plus one, subtracting two to the power k produces a zero follower. A reference heap of size two to the power k plus one leaves only one higher removal to count; lower followers bounded by B give the bound B plus two.

**Theorem 1.5 (Apply the paired pivot after a lower move).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.lower_paired_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.lower_paired_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing a higher-depth heap by two to the power k beneath a unique depth k plus one heap creates the paired-pivot configuration. If its lower followers have value at most B, its value is at most B plus two.

**Theorem 1.6 (No unique minimum-depth heap).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.multiple_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.multiple_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the minimum-depth count is not one, a nonzero position has only zero higher-depth followers. A bound B on lower-depth followers gives value at most B plus one.

**Theorem 1.7 (Seven beside one depth-one heap).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.seven_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.seven_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A board containing seven, with all other heaps even and exactly one at depth one, has value at most six. Removals one and five on seven both give zero; all removals on other heaps give zero.

**Theorem 1.8 (A distinguished heap of size two).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.two_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.two_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive position containing a heap of size two has value at most four, regardless of the other heap sizes and their number.

**Theorem 1.9 (Odd removals beside four).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.four_lower_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.four_lower_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From a positive-depth board containing four, every odd removal produces a follower of value at most four. The reference heap either remains four or becomes a positive odd heap at most three.

**Theorem 1.10 (A distinguished heap of size four).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.four_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.four_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive position containing a heap of size four has value at most eight. The unique-depth case uses the paired pivot after a removal of size two.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.four_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.four_lower_odd`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.lower_paired_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.multiple_step`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.paired_pivot_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.paired_remainder_zero`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.power_divisor_high`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.refined_step`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.seven_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundSmall.two_bound`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundOutcome](DivisorNimBoundOutcome.md)
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundReference](DivisorNimBoundReference.md)
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundSmallSupport](DivisorNimBoundSmallSupport.md)
