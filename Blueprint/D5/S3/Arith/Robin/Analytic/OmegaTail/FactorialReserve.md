# Prime reserves at a fixed factorial order

## Abstract

The literal factorial threshold, its rounded reserves, and the retained prime base.

**Definition 1.1 (Centered factorial threshold).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.centeredThreshold`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.centeredThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a real prime cutoff P, multiply P by the sum of j!/(log P)^(j+1) over 0 ≤ j < r.

**Definition 1.2 (Factorial threshold).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.threshold`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.threshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the centered threshold at log x.

**Definition 1.3 (Strict counting function).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.tailCount`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.tailCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count integers from one through the natural floor of x whose number of distinct prime factors strictly exceeds the factorial threshold.

**Definition 1.4 (Integer cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.cutoff`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.cutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the natural floor of the centered threshold and add one.

**Definition 1.5 (Real prime excess).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.primeExcess`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.primeExcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the integer cutoff from the number of primes at most P in real arithmetic.

**Definition 1.6 (Deletion count).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.deletionCount`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.deletionCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use natural subtraction for the size of the deleted prime set.

**Definition 1.7 (Continuous reserve).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.continuousReserve`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.continuousReserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add P minus theta(P) to the unrounded prime excess times log P.

**Definition 1.8 (Rounded reserve).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.roundedReserve`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.roundedReserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the real prime excess times log P to P minus theta(P).

**Definition 1.9 (Far deletion reserve).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.safeReserve`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.safeReserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the real prime excess times log(P/2) to P minus theta(P).

**Theorem 1.10 (Exact counting at exp P).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.tailCount_exp_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.tailCount_exp_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P > 1 the strict inequality in the counting function is equivalent to meeting the integer cutoff, including when the threshold is an integer.

**Theorem 1.11 (Continuous reserve limit).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.continuous_reserve_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.continuous_reserve_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each fixed order r the continuous reserve divided by P/(log P)^r tends to r!. Multiplying the prime-counting residual by log P changes its scale from P/(log P)^(r+1) to P/(log P)^r. The theta deficit divided by the latter scale tends to zero.

**Theorem 1.12 (Factorial reserve limits).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.factorial_reserve`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.factorial_reserve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each fixed order r, the real prime excess divided by P/(log P)^(r+1) tends to r!. The floor error is at most one and vanishes on this scale. Eventually the natural deletion count casts to the real excess. The theta error is negligible on the scale P/(log P)^r and log(P/2)/log P tends to one. Both reserves divided by P/(log P)^r therefore tend to r!.

**Theorem 1.13 (Exact far deletion).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.factorial_far_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.factorial_far_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix r ≥ 2. Eventually the desired deletion count is below the capacity of the prime window (P/2, 3P/4]. Every subset of the prescribed size leaves exactly the integer cutoff of distinct primes. All primes at most P outside the window are retained, and the logarithm of the retained product is at most P minus the far deletion reserve.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.centeredThreshold`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.continuousReserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.continuous_reserve_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.cutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.deletionCount`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.factorial_far_deletion`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.factorial_reserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.primeExcess`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.roundedReserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.safeReserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.tailCount`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.tailCount_exp_eq`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve.threshold`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion](FarDeletion.md)
