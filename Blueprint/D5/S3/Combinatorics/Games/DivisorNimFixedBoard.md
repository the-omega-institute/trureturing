# Fixed-board Divisor Nim sequences

## Abstract

The actual fixed-board sequence has an eventual period, and its least positive eventual period divides every eventual period.

A position is a finite multiset of positive natural heap sizes. A move selects one occurrence h and removes an amount d between one and h that divides every untouched occurrence. A zero remainder is deleted. The empty position has value zero. The function adjoinHeap omits a varying heap at n=0, and fixedSequence is the actual native Grundy value of this position. Heap sizes, cardinalities and repeated occurrences are unrestricted.

**Theorem 1.1 (The exact bridge for the zero convention).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.tail_period_iff_fixed_sequence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.tail_period_iff_fixed_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Takayuki Morisawa (2026). *Winning strategy and periodicity of m-pile divisor Nim*. DOI: [10.1007/s00182-026-00991-5](https://doi.org/10.1007/s00182-026-00991-5). URL: <https://doi.org/10.1007/s00182-026-00991-5>.

*Commentary.*

For every fixed multiset A and natural T, the existing HasTailPeriod A T holds exactly when the omission-aware actual sequence fixedSequence A has eventual period T. Increasing a threshold by one ensures both varying indices are positive. Thus the least eventual period is unchanged by omitting the varying zero heap.

**Theorem 1.2 (Selected fixed moves).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.mem_fixedMoveData`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.mem_fixedMoveData` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Takayuki Morisawa (2026). *Winning strategy and periodicity of m-pile divisor Nim*. DOI: [10.1007/s00182-026-00991-5](https://doi.org/10.1007/s00182-026-00991-5). URL: <https://doi.org/10.1007/s00182-026-00991-5>.

*Commentary.*

For every multiset A and natural h,d, the pair (h,d) belongs to fixedMoveData A exactly when h is an occurrence in A and legal A h d holds. Erasing h removes one occurrence; equal heap sizes do not impose distinctness.

**Theorem 1.3 (Equality of the actual follower sets).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Takayuki Morisawa (2026). *Winning strategy and periodicity of m-pile divisor Nim*. DOI: [10.1007/s00182-026-00991-5](https://doi.org/10.1007/s00182-026-00991-5). URL: <https://doi.org/10.1007/s00182-026-00991-5>.

*Commentary.*

Let A be positive and nonempty, and n at least gcd(A). The actual follower-value set of adjoinHeap A n equals the union of fixedSequence A (n-d), over every positive divisor d of gcd(A), and fixedMoveValues A n. The latter set contains fixedSequence (successor A h d) n for every actual fixed move with d dividing n. It includes an empty fixed successor and legal deletion. Both inclusions hold.

**Theorem 1.4 (Eventual periods for every nonempty fixed board).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_eventually_periodic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_eventually_periodic` (`✓ std3`). ∎

*Citation.* Takayuki Morisawa (2026). *Winning strategy and periodicity of m-pile divisor Nim*. DOI: [10.1007/s00182-026-00991-5](https://doi.org/10.1007/s00182-026-00991-5). URL: <https://doi.org/10.1007/s00182-026-00991-5>.

*Commentary.*

For every positive nonempty multiset A there is a positive natural T and a threshold N such that g((n+T) adjoined to A)=g(n adjoined to A) for all n at least N. Induction on the total fixed stones supplies periods for all nonempty fixed successors. Their periods and every legal removal amount have a common positive multiple. A single threshold works for the finitely many fixed moves.

The uniform bound confines tail values to zero through twice the fixed sum. Deleting the sole fixed heap leaves a singleton of actual value n, which exceeds this bound on the tail and does not affect the mex. Full gcd-length blocks sampled at the same forcing phase lie in a finite set. Two equal blocks propagate by the exact native recurrence and give a positive period.

**Theorem 1.5 (Divisibility of the least period).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_least_period`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_least_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Takayuki Morisawa (2026). *Winning strategy and periodicity of m-pile divisor Nim*. DOI: [10.1007/s00182-026-00991-5](https://doi.org/10.1007/s00182-026-00991-5). URL: <https://doi.org/10.1007/s00182-026-00991-5>.

*Commentary.*

For every positive nonempty A, leastTailPeriod A is positive, is an eventual period, and divides every eventual period T. Differences of ordered tail periods are tail periods. Reducing T modulo the least positive period therefore forces zero remainder. The value at n=0 retains its omission convention.

**Theorem 1.6 (The actual minimum heap).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_minimum_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_minimum_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Takayuki Morisawa (2026). *Winning strategy and periodicity of m-pile divisor Nim*. DOI: [10.1007/s00182-026-00991-5](https://doi.org/10.1007/s00182-026-00991-5). URL: <https://doi.org/10.1007/s00182-026-00991-5>.

*Commentary.*

For every nonempty multiset A, fixedMinimum A belongs to A and is at most every member of A. The definition assigns zero to the empty multiset.

**Theorem 1.7 (The complete periodic fixed-option signal).**

Lean statement: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.comparison_spacing_signal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.comparison_spacing_signal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Takayuki Morisawa (2026). *Winning strategy and periodicity of m-pile divisor Nim*. DOI: [10.1007/s00182-026-00991-5](https://doi.org/10.1007/s00182-026-00991-5). URL: <https://doi.org/10.1007/s00182-026-00991-5>.

*Commentary.*

Let A be positive and nonempty and H its minimum. The comparisonSpacing A is the least common multiple of lcm(1,...,H) and the leastTailPeriod values of every nonempty actual direct fixed successor. It is positive, is divisible by lcm(1,...,H), and is divisible by each of these actual least periods. The whole set fixedValues A n of nonempty fixed-follower SG values repeats after this spacing for every sufficiently large n. The empty fixed successor is retained separately in the literal recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.comparison_spacing_signal`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_eventually_periodic`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_least_period`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_board_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.fixed_minimum_spec`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.mem_fixedMoveData`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimFixedBoard.tail_period_iff_fixed_sequence`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimGcdSixSource](DivisorNimGcdSixSource.md)
