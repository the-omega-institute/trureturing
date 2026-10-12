# Finite binary reversal avoids arithmetic progressions

## Abstract

Reversing a fixed number of binary digits gives a finite order in which no nonconstant three-term arithmetic progression occurs as a subsequence.

**Definition 1.1 (Binary reversal).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank`

*Formalization.* `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For zero bits the rank is zero. For one more bit, the lowest bit contributes two to the power of the previous bit count, and the remaining contribution is the rank of the quotient by two with the previous bit count.

**Theorem 1.2 (The rank fits within the bit bound).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every bit count and natural input, the rank is strictly below two raised to the bit count.

**Theorem 1.3 (Injectivity on bounded inputs).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both inputs are strictly below two raised to the bit count and their ranks agree, the inputs agree. The highest reversed digit determines parity, and induction determines the quotients by two.

**Theorem 1.4 (No monotone arithmetic progression).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_no_ap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_no_ap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any three inputs strictly below the same power of two whose endpoints sum to twice the middle input, the three ranks cannot be strictly increasing. The endpoints have the same parity. If the middle parity differs, its rank is an extreme; otherwise division by two preserves the progression and induction applies.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_injective`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_lt`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.rank_no_ap`
