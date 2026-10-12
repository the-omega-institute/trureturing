# Divisor Nim and Minimum Excluded Values

## Abstract

The literal divisor rule gives a finite move set and a recursion on total stones.

**Definition 1.1 (Heap multisets).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.Position`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.Position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A position is a finite multiset of natural heap sizes.

**Definition 1.2 (Positive heaps).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.Positive`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.Positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every heap appearing in the position has positive size.

**Definition 1.3 (A common divisor).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.dividesAll`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.dividesAll` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The removal amount divides every heap in the given multiset.

**Definition 1.4 (Replace one heap).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.successor`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.successor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase one occurrence of h and insert h minus d when this remainder is positive.

**Definition 1.5 (Legal removal).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.legal`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amount d is positive, is at most h, and divides every heap left after erasing one occurrence of h.

**Definition 1.6 (All followers).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.moves`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.moves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each occurring heap h, include each replacement by a legal amount from one through h.

**Theorem 1.7 (Stone count decreases).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.successor_sum_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.successor_sum_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing an occurring heap by its remainder under a legal positive removal strictly decreases the multiset sum.

**Definition 1.8 (Sprague–Grundy value).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recursion on the multiset sum takes the least natural number absent from the finite set of follower values.

**Theorem 1.9 (Every follower is smaller).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.move_sum_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.move_sum_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every follower has strictly fewer stones than its parent.

**Theorem 1.10 (The mex equation).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value of a position equals the minimum excluded natural number of the values of its followers.

**Theorem 1.11 (The current value is excluded).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_not_follower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_not_follower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No follower has the same Grundy value as the current position.

**Theorem 1.12 (Smaller values are attained).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.follower_mem_of_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.follower_mem_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural number smaller than the current Grundy value is the value of some follower.

**Theorem 1.13 (Mex and cardinality).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.mex_le_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.mex_le_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum excluded natural number of a finite set is at most its cardinality.

**Theorem 1.14 (Count distinct exceptional values).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.mex_counting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.mex_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every element of s is at most B or belongs to E, then the mex of s is at most B plus the cardinality of E plus one.

**Theorem 1.15 (Count exceptional followers).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_counting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every follower has value at most B or belongs to a finite set E, the current value is at most B plus the cardinality of E plus one.

**Theorem 1.16 (Bounded follower values).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_le_of_followers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_le_of_followers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every follower value is at most B, the current value is at most B plus one.

**Theorem 1.17 (Zero and its followers).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A position has value zero exactly when every follower has nonzero value.

**Definition 1.18 (The twice-minimum bound).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimGrundy.claim`

*Formalization.* `D5/S3/Combinatorics/Games/DivisorNimGrundy.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every nonempty positive heap multiset and each smallest occurring heap m, the Grundy value is at most twice m.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.Position`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.Positive`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.claim`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.dividesAll`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.follower_mem_of_lt`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_counting`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_eq`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_le_of_followers`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_not_follower`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.grundy_zero_iff`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.legal`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.mex_counting`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.mex_le_card`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.move_sum_lt`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.moves`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.successor`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimGrundy.successor_sum_lt`
- Dependency: [D5/S0/Certificates/Games/CrimGrundyRefutation](../../../S0/Certificates/Games/CrimGrundyRefutation.md)
